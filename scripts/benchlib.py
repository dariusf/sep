import re
from collections import Counter, defaultdict

OUTCOMES = ["proved", "failed", "unsupported", "parse-error", "timeout", "invalid"]


def normalize(reason):
    reason = reason.split("⊢")[0]
    reason = re.sub(r"\bv_\w+", "v", reason)
    reason = re.sub(r"x✝[⁰¹²³⁴⁵⁶⁷⁸⁹]*", "x", reason)
    reason = re.sub(r"case (a\.)*a\b", "case a", reason)
    reason = re.sub(r"\d+", "N", reason)
    reason = re.sub(r"\s+", " ", reason)
    reason = re.sub(r"(v )+", "v ", reason)
    reason = re.sub(r"(x )+", "x ", reason)
    return reason.strip()[:100]


def ms_of(r):
    try:
        return int(r["ms"])
    except (ValueError, KeyError):
        return 0


def by_dir(rows):
    d = defaultdict(list)
    for r in rows:
        d[r["dir"]].append(r)
    return d


def dir_summary(rows):
    lines = []
    for d, rs in sorted(by_dir(rows).items()):
        c = Counter(r["outcome"] for r in rs)
        detail = " ".join("%s=%d" % (o, c[o]) for o in OUTCOMES if c[o])
        lines.append("%s: n=%d %s total=%dms" % (d, len(rs), detail, sum(ms_of(r) for r in rs)))
    return "\n".join(lines)


def outcome_table(rows):
    lines = []
    for d, rs in sorted(by_dir(rows).items()):
        lines.append("[%s]  (name outcome ms; p=proved f=failed t=timeout i=invalid u=unsupported e=parse-error)" % d)
        for r in sorted(rs, key=lambda r: r["file"]):
            name = r["file"][:-5] if r["file"].endswith(".smt2") else r["file"]
            lines.append("%s %s %d" % (name, r["outcome"][0], ms_of(r)))
    return "\n".join(lines)


def reason_groups(rows, limit=12):
    groups = defaultdict(list)
    for r in rows:
        if r["outcome"] != "proved":
            groups[(r["outcome"], normalize(r.get("reason", "")))].append(r)
    ordered = sorted(groups.items(), key=lambda kv: -len(kv[1]))[:limit]
    lines = []
    for (o, reason), rs in ordered:
        ex = " ".join(r["file"] for r in rs[:3])
        lines.append("%dx %s: %s  e.g. %s" % (len(rs), o, reason or "(no reason)", ex))
    return "\n".join(lines)


def slowest_proved(rows, limit=15):
    ps = sorted((r for r in rows if r["outcome"] == "proved"), key=ms_of, reverse=True)[:limit]
    return " ".join("%s=%dms" % (r["file"], ms_of(r)) for r in ps)


def totals(rows, timeout_ms):
    n = len(rows)
    proved = sum(1 for r in rows if r["outcome"] == "proved")
    timeouts = sum(1 for r in rows if r["outcome"] == "timeout")
    total_ms = sum(ms_of(r) for r in rows)
    return n, proved, timeouts, total_ms, n * timeout_ms


def text_report(rows, timeout_ms):
    n, proved, timeouts, total_ms, worst = totals(rows, timeout_ms)
    head = "proved=%d/%d timeouts=%d (%dms of %dms total, worst case %dms)" % (
        proved, n, timeouts, timeouts * timeout_ms, total_ms, worst)
    return "\n\n".join([head, dir_summary(rows), reason_groups(rows), outcome_table(rows)])
