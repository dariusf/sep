#!/usr/bin/env python3
import argparse
import glob
import json
import os
import re

TIME_WEIGHT = 0.2
LINE_WEIGHT = 0.00002
INVALID_TIME_WEIGHT = 0.2


def load_programs(out_dir):
    cps = glob.glob(os.path.join(out_dir, "checkpoints", "checkpoint_*"))
    if not cps:
        return {}, None
    latest = max(cps, key=lambda p: int(p.rsplit("_", 1)[1]))
    programs = {}
    for f in glob.glob(os.path.join(latest, "programs", "*.json")):
        d = json.load(open(f))
        a = d.get("artifacts_json") or {}
        if isinstance(a, str):
            try:
                a = json.loads(a)
            except ValueError:
                a = {}
        d["artifacts"] = a
        programs[d["id"]] = d
    return programs, latest


def outcomes(program):
    t = {}
    d = None
    for l in program["artifacts"].get("outcomes", "").splitlines():
        if l.startswith("["):
            d = l[1 : l.index("]")]
            continue
        parts = l.split()
        if len(parts) == 3:
            t[(d, parts[0])] = parts[1]
    return t


def diff(child, parent):
    tc, tp = outcomes(child), outcomes(parent)
    gained = sorted(k[1] for k in tc if tc[k] == "p" and tp.get(k) not in (None, "p"))
    lost = sorted(k[1] for k in tc if tc[k] != "p" and tp.get(k) == "p")
    return gained, lost


def iteration_of(p):
    return p.get("iteration_found", p.get("generation", 0))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out", nargs="?", default="evolve/out")
    ap.add_argument("-v", action="store_true", help="show gained/lost problems per program")
    args = ap.parse_args()
    programs, cp = load_programs(args.out)
    if not programs:
        print("no checkpoints under", args.out)
        return
    print("checkpoint:", os.path.basename(cp))
    order = sorted(programs.values(), key=lambda p: (iteration_of(p), p.get("timestamp", 0)))
    best = max(order, key=lambda p: p["metrics"].get("combined_score", 0))
    print("%4s %-8s %-8s %5s %7s %6s %5s %7s %7s %7s %7s %s" % (
        "iter", "id", "parent", "prov", "time_s", "inv_s", "lines",
        "score", "-time", "-lines", "-inval", ""))
    for p in order:
        m = p["metrics"]
        if m.get("n", 0) == 0:
            reason = p["artifacts"].get("failure_reason", "no result")
            print("%4d %-8s %-8s %s" % (iteration_of(p), p["id"][:8], (p.get("parent_id") or "")[:8], reason))
            continue
        inv_s = ""
        mt = re.search(r"time on invalid\s+(\d+)s", p["artifacts"].get("totals", ""))
        if mt:
            inv_s = mt.group(1)
        mark = " best" if p["id"] == best["id"] else ""
        print("%4d %-8s %-8s %5d %7d %6s %5d %7.4f %7.4f %7.4f %7.4f%s" % (
            iteration_of(p), p["id"][:8], (p.get("parent_id") or "")[:8], m.get("proved", 0),
            m.get("total_ms", 0) / 1000, inv_s, m.get("lines", 0), m.get("combined_score", 0),
            TIME_WEIGHT * m.get("time_score", 0), LINE_WEIGHT * m.get("lines", 0),
            INVALID_TIME_WEIGHT * m.get("invalid_time_score", 0), mark))
        if args.v and p.get("parent_id") in programs:
            gained, lost = diff(p, programs[p["parent_id"]])
            if gained or lost:
                print("     gained: %s" % " ".join(gained))
                print("     lost:   %s" % " ".join(lost))
        if args.v:
            desc = (p.get("metadata") or {}).get("changes", "")
            if desc:
                first = desc.strip().splitlines()[0][:100]
                print("     change: %s" % first)


main()
