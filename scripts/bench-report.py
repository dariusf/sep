#!/usr/bin/env python3
import argparse
import csv
import html
import os
import sys
from collections import Counter, defaultdict
from string import Template

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from benchlib import OUTCOMES, normalize, text_report

PAGE = Template("""<!doctype html>
<html><head><meta charset="utf-8"><title>bench report</title>
<style>
body{font:14px/1.4 -apple-system,Helvetica,Arial,sans-serif;margin:2em;color:#222}
h1{font-size:1.4em}h2{font-size:1.1em;margin-top:2em}
table{border-collapse:collapse;margin:.5em 0}
th,td{border:1px solid #ddd;padding:.3em .6em;text-align:right;vertical-align:top}
th:first-child,td:first-child{text-align:left}
th{background:#f4f4f4}
tr.total td{font-weight:bold}
.proved{color:#1a7f37}.failed{color:#b42318}.unsupported{color:#9a6700}.timeout{color:#8250df}.parse-error{color:#b42318}
.bar{display:inline-block;height:.8em;background:#1a7f37;vertical-align:middle}
.bar.rest{background:#e5e5e5}
details{margin:.3em 0}summary{cursor:pointer}
pre{white-space:pre-wrap;background:#f8f8f8;padding:.4em .6em;font-size:12px;margin:.2em 0}
td.reason{text-align:left;max-width:60em;font-family:ui-monospace,monospace;font-size:12px;white-space:pre-wrap}
input{margin:.5em 0;padding:.3em;width:20em}
</style></head><body>
<h1>bench report</h1>
<p>$source &middot; $n problems &middot; <span class="proved">$proved proved</span> ($pct%) &middot; $total_s s total</p>
<h2>per directory</h2>
<table>
<tr><th>dir</th><th>n</th><th>proved</th><th></th><th>failed</th><th>unsupported</th><th>parse-error</th><th>timeout</th><th>ms</th><th>mean ms</th></tr>
$dir_rows
</table>
<h2>failure reasons</h2>
$reason_blocks
<h2>all problems</h2>
<input id="q" placeholder="filter by name, outcome or reason" oninput="f()">
<table id="all">
<tr><th>problem</th><th>outcome</th><th>ms</th><th>reason</th></tr>
$all_rows
</table>
<script>
function f(){var q=document.getElementById('q').value.toLowerCase();
for(const r of document.querySelectorAll('#all tr')){if(!r.cells[3])continue;
r.style.display=r.textContent.toLowerCase().includes(q)?'':'none'}}
</script>
</body></html>
""")


def esc(s):
    return html.escape(str(s))


def dir_row(name, rs, total=False):
    c = Counter(r["outcome"] for r in rs)
    ms = sum(int(r["ms"]) for r in rs)
    n = len(rs)
    pct = 100 * c["proved"] / n if n else 0
    bar = '<span class="bar" style="width:%dpx"></span><span class="bar rest" style="width:%dpx"></span>' % (pct, 100 - pct)
    cells = [esc(name), n, '<span class="proved">%d</span>' % c["proved"], bar]
    cells += ['<span class="%s">%d</span>' % (o, c[o]) if c[o] else "0" for o in OUTCOMES[1:]]
    cells += [ms, ms // n if n else 0]
    return '<tr%s>%s</tr>' % (' class="total"' if total else "", "".join("<td>%s</td>" % x for x in cells))


def reason_block(outcome, reason, rs):
    examples = "".join(
        "<li>%s/%s<pre>%s</pre></li>" % (esc(r["dir"]), esc(r["file"]), esc(r["reason"])) for r in rs[:3]
    )
    return (
        '<details><summary><b>%d</b> <span class="%s">%s</span> <code>%s</code></summary><ul>%s</ul></details>'
        % (len(rs), outcome, outcome, esc(reason), examples)
    )


def all_row(r):
    return '<tr><td>%s/%s</td><td class="%s">%s</td><td>%s</td><td class="reason">%s</td></tr>' % (
        esc(r["dir"]), esc(r["file"]), r["outcome"], r["outcome"], r["ms"], esc(r["reason"])
    )


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("csv", nargs="?", default="bench-results.csv")
    ap.add_argument("dir", nargs="?")
    ap.add_argument("-o", "--out", default="bench-report.html")
    ap.add_argument("--text", action="store_true")
    ap.add_argument("--timeout", type=int, default=5000)
    args = ap.parse_args()
    rows = list(csv.DictReader(open(args.csv)))
    if args.dir:
        rows = [r for r in rows if r["dir"] == args.dir]
    if args.text:
        print(text_report(rows, args.timeout))
        return

    by_dir = defaultdict(list)
    for r in rows:
        by_dir[r["dir"]].append(r)
    dir_rows = "\n".join(dir_row(d, by_dir[d]) for d in sorted(by_dir))
    dir_rows += "\n" + dir_row("total", rows, total=True)

    groups = defaultdict(list)
    for r in rows:
        if r["outcome"] != "proved":
            groups[(r["outcome"], normalize(r["reason"]))].append(r)
    reason_blocks = "\n".join(
        reason_block(o, reason, rs) for (o, reason), rs in sorted(groups.items(), key=lambda kv: -len(kv[1]))
    ) or "<p>none</p>"

    n = len(rows)
    proved = sum(1 for r in rows if r["outcome"] == "proved")
    total_ms = sum(int(r["ms"]) for r in rows)
    page = PAGE.substitute(
        source=esc(args.csv),
        n=n,
        proved=proved,
        pct="%.1f" % (100 * proved / n if n else 0),
        total_s="%.1f" % (total_ms / 1000),
        dir_rows=dir_rows,
        reason_blocks=reason_blocks,
        all_rows="\n".join(all_row(r) for r in rows),
    )
    with open(args.out, "w") as f:
        f.write(page)
    print("%s: %d/%d proved, %d ms -> %s" % (args.csv, proved, n, total_ms, args.out))


main()
