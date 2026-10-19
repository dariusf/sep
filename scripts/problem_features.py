import csv
import glob
import json
import os
import re
import sys
from collections import Counter, defaultdict



def tokenize(s):
    s = re.sub(r";[^\n]*", "", s)
    s = re.sub(r"\|[^|]*\|", "", s)
    return re.findall(r"\(|\)|[^\s()]+", s)


def parse(tokens):
    stack = [[]]
    for t in tokens:
        if t == "(":
            stack.append([])
        elif t == ")":
            e = stack.pop()
            stack[-1].append(e)
        else:
            stack[-1].append(t)
    return stack[0]


def head(e):
    return e[0] if isinstance(e, list) and e else None


def atoms(e, acc):
    if not isinstance(e, list):
        return
    h = head(e)
    if h in ("and", "sep"):
        for x in e[1:]:
            atoms(x, acc)
    elif h == "exists":
        acc["exists"] += 1
        atoms(e[2], acc)
    elif h == "or":
        acc["or"] += 1
        for x in e[1:]:
            atoms(x, acc)
    elif h == "not":
        atoms(e[1], acc)
    elif h == "pto":
        acc["pto"].append((e[1], e[2][1:] if isinstance(e[2], list) else []))
    elif h == "=":
        acc["eq"].append((e[1], e[2]))
    elif h == "distinct":
        acc["ne"].append(tuple(e[1:]))
    elif h == "_" and len(e) > 1 and e[1] == "emp":
        acc["emp"] += 1
    elif h == "as":
        pass
    elif isinstance(h, str) and h in acc["preds_known"]:
        acc["pred"].append((h, e[1:]))
    elif isinstance(h, str):
        acc["other"].append(h)


def new_acc(preds):
    return {"pto": [], "pred": [], "eq": [], "ne": [], "exists": 0, "or": 0, "emp": 0,
            "other": [], "preds_known": preds}


def loc(x):
    if isinstance(x, list) and head(x) == "as":
        return "nil"
    return x if isinstance(x, str) else "?"


def analyze(path):
    text = open(path, errors="ignore").read()
    m = re.search(r":status (\w+)", text)
    status = m.group(1) if m else "?"
    sexp = parse(tokenize(text))
    preds = {}
    mutual = False
    fields = 0
    for e in sexp:
        h = head(e)
        if h == "declare-datatypes":
            for ctor in e[2]:
                for c in ctor:
                    if isinstance(c, list):
                        fields = max(fields, len(c) - 1)
        if h == "define-fun-rec":
            preds[e[1]] = (e[2], e[4])
        if h == "define-funs-rec":
            mutual = len(e[1]) > 1
            for decl, body in zip(e[1], e[2]):
                preds[decl[0]] = (decl[1], body)
    pinfo = {}
    for name, (params, body) in preds.items():
        acc = new_acc(set(preds))
        atoms(body, acc)
        rec = sum(1 for p, _ in acc["pred"] if p == name)
        calls_other = sorted(set(p for p, _ in acc["pred"] if p != name))
        int_args = sum(1 for p in params if isinstance(p, list) and p[1] == "Int")
        branches = 0
        if head(body) == "or":
            branches = len(body) - 1
        pinfo[name] = dict(arity=len(params), rec=rec, other=calls_other, ints=int_args,
                           branches=branches, ptos=len(acc["pto"]), exists=acc["exists"])
    asserts = [e for e in sexp if head(e) == "assert"]
    if len(asserts) != 2:
        return None
    L = new_acc(set(preds))
    R = new_acc(set(preds))
    atoms(asserts[0][1], L)
    atoms(asserts[1][1], R)
    feats = set()
    if status == "sat":
        feats.add("invalid")
    lpred = {(p, tuple(loc(a) for a in args)) for p, args in L["pred"]}
    rpred = {(p, tuple(loc(a) for a in args)) for p, args in R["pred"]}
    lpto = {loc(a) for a, _ in L["pto"]}
    lstarts = {(p, a[0]) for p, a in lpred}
    lends = defaultdict(set)
    for p, a in lpred:
        if len(a) >= 2:
            lends[(p, a[0])].add(a[1])
    ptonext = defaultdict(set)
    for a, vals in L["pto"]:
        for v in vals:
            ptonext[loc(a)].add(loc(v))
    if not rpred and not R["pto"] and R["emp"]:
        feats.add("rhs_emp")
    unmatched = rpred - lpred
    if not unmatched and set(loc(a) for a, _ in R["pto"]) <= lpto and not R["exists"]:
        feats.add("cancel_only")
    for p, a in unmatched:
        if len(a) < 2:
            feats.add("fold_other")
            continue
        src = a[0]
        if src in lpto:
            feats.add("fold_pto")
        if (p, src) in lstarts and a[1] not in lends[(p, src)]:
            feats.add("compose_seg")
        if src not in lpto and (p, src) not in lstarts:
            feats.add("fold_other")
    if any(len(a) >= 2 and a[0] == a[1] for p, a in rpred):
        feats.add("rhs_empty_seg")
    if R["exists"]:
        feats.add("rhs_exists")
    if R["or"] or L["or"]:
        feats.add("top_or")
    if L["pto"] and not L["ne"] and any(pi["branches"] >= 2 for pi in pinfo.values()):
        feats.add("alloc_neq")
    if any(pi["rec"] >= 2 for pi in pinfo.values()):
        feats.add("tree_pred")
    if any(pi["other"] for pi in pinfo.values()):
        feats.add("nested_pred")
    if mutual:
        feats.add("mutual")
    if any(pi["ints"] for pi in pinfo.values()):
        feats.add("int_args")
    if fields >= 2:
        feats.add("multi_field")
    if len(lpred) + len(L["pto"]) >= 12:
        feats.add("large")
    if len(preds) >= 2 and not mutual:
        feats.add("several_preds")
    names = sorted(preds)
    return dict(status=status, feats=sorted(feats), preds=names, natoms=len(lpred) + len(L["pto"]),
                nrhs=len(rpred) + len(R["pto"]))


FEATURE_DOC = """invalid: status sat, the entailment does not hold; never provable, only fail fast
cancel_only: every RHS atom occurs on the LHS, no RHS existential
rhs_emp: RHS is emp
fold_pto: an RHS predicate starts at an LHS points-to cell (fold cells into the predicate)
compose_seg: an RHS segment spans two chained LHS segments (needs segment composition)
fold_other: an RHS predicate matched by no LHS atom (unfold/fold by other means)
alloc_neq: predicates carry disequality guards, LHS has cells but no explicit distinct facts (derive x != y from separate allocation)
nested_pred: a predicate body calls another predicate
mutual: define-funs-rec group
several_preds: more than one predicate, not mutual
tree_pred: a predicate body has two recursive calls
multi_field: cells with two or more fields
large: 12 or more LHS atoms"""


def scan(bench_root, dirs):
    rows = {}
    for d in dirs:
        for f in sorted(os.listdir(os.path.join(bench_root, d))):
            if f.endswith(".smt2"):
                r = analyze(os.path.join(bench_root, d, f))
                if r is not None:
                    rows[(d, f)] = r
    return rows


def status_of(bench_root, d, f):
    m = re.search(r":status (\w+)", open(os.path.join(bench_root, d, f), errors="ignore").read())
    return m.group(1) if m else "?"


def _combos(feats):
    combos = defaultdict(list)
    for key, r in feats.items():
        if "invalid" not in r["feats"]:
            combos[tuple(r["feats"])].append(key)
    return sorted(combos.items(), key=lambda kv: -len(kv[1]))


def static_report(feats):
    lines = [FEATURE_DOC, "", "feature set: n  examples"]
    for fs, keys in _combos(feats):
        ex = " ".join(k[1][:-5] for k in keys[:2])
        lines.append("%s: %d  %s" % (" ".join(fs) or "(none)", len(keys), ex))
    return "\n".join(lines)


def feature_report(feats, outcomes):
    lines = ["feature set: n proved failed  (example unproved)"]
    for fs, keys in _combos(feats):
        p = sum(1 for k in keys if outcomes.get(k) == "proved")
        ex = [k[1][:-5] for k in keys if outcomes.get(k) != "proved"][:2]
        lines.append("%s: %d %d %d  %s" % (" ".join(fs) or "(none)", len(keys), p, len(keys) - p, " ".join(ex)))
    return "\n".join(lines)


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else "sl-comp-bench"
    csv_path = sys.argv[2] if len(sys.argv) > 2 else None
    dirs = sys.argv[3].split(",") if len(sys.argv) > 3 else sorted(
        d for d in os.listdir(root) if d.endswith("_entl"))
    feats = scan(root, dirs)
    if csv_path in (None, "-"):
        print(static_report(feats))
        return
    outcomes = {}
    for r in csv.DictReader(open(csv_path)):
        outcomes[(r["dir"], r["file"])] = r["outcome"]
    print(feature_report(feats, outcomes))


if __name__ == "__main__":
    main()
