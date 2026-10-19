import csv
import hashlib
import os
import re
import shutil
import subprocess
import sys
import tempfile

from openevolve.evaluation_result import EvaluationResult

HERE = os.path.dirname(os.path.abspath(__file__))
MAIN = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(MAIN, "scripts"))
from benchlib import dir_summary, ms_of, outcome_table, reason_groups, slowest_proved, totals
from problem_features import feature_report, scan, status_of
DEFAULT_WORKTREE = os.path.join(MAIN, ".claude", "worktrees", "evolve")
TARGET = "Sep/Xsearch.lean"
BENCH_TIMEOUT_MS = 5000
PROVED_MARGIN_MS = 4000
EDGE_MS = 3500
TIME_WEIGHT = 0.2
LINE_WEIGHT = 0.00002
INVALID_TIME_WEIGHT = 0.2
LINE_WIDTH = 80


def _dirs(var, default):
    v = os.environ.get(var)
    if v is None:
        return default
    return [d for d in v.split(",") if d]


STAGE1_DIRS = _dirs("EVOLVE_STAGE1_DIRS", ["qf_shls_entl", "yolo"])
STAGE2_DIRS = _dirs("EVOLVE_STAGE2_DIRS", [])

FORBIDDEN = [
    "sorry",
    "admit",
    "axiom",
    "native_decide",
    "unsafe",
    "implemented_by",
    "ofReduceBool",
    "extern",
]

BUILD_TIMEOUT_S = 1800
STAGE1_RUN_TIMEOUT_S = 1800
FULL_RUN_TIMEOUT_S = 5400


def _worktree():
    return os.environ.get("EVOLVE_WORKTREE", DEFAULT_WORKTREE)


def _zero(reason, lines=0.0, **artifacts):
    metrics = {
        "combined_score": 0.0,
        "proved": 0.0,
        "n": 0.0,
        "total_ms": 0.0,
        "proved_fraction": 0.0,
        "time_score": 0.0,
        "lines": float(lines),
        "invalid_time_score": 0.0,
    }
    arts = {"failure_reason": reason}
    arts.update(artifacts)
    return EvaluationResult(metrics=metrics, artifacts=arts)


def _score_table(stage, proved, n, timeouts, total_ms, n_invalid, invalid_ms, invalid_worst,
                 lines, proved_fraction, time_score, invalid_time_score, combined, csv_name):
    rows = [
        ("proved", "%d/%d" % (proved, n), "+%.4f" % proved_fraction),
        ("time on provable", "%ds, %d timeouts" % (total_ms // 1000, timeouts),
         "-%.4f" % (TIME_WEIGHT * time_score)),
        ("effective lines", "%d" % lines, "-%.4f" % (LINE_WEIGHT * lines)),
        ("time on invalid", "%ds of %ds worst case (%d problems)"
         % (invalid_ms // 1000, invalid_worst // 1000, n_invalid),
         "-%.4f" % (INVALID_TIME_WEIGHT * invalid_time_score)),
        ("score", "", "%.4f" % combined),
    ]
    w = max(len(r[1]) for r in rows)
    lines_out = ["stage=%s  full csv: %s" % (stage, csv_name)]
    for k, v, c in rows:
        lines_out.append("%-18s %-*s %s" % (k, w, v, c))
    return "\n".join(lines_out)


def _effective_lines(source):
    start = source.find("EVOLVE-BLOCK-START")
    end = source.find("EVOLVE-BLOCK-END")
    block = source[start:end] if 0 <= start < end else source
    n = 0
    for line in block.splitlines():
        if line.strip():
            n += max(1, -(-len(line) // LINE_WIDTH))
    return n


def _label(rows, wt):
    for r in rows:
        r["status"] = status_of(os.path.join(wt, "sl-comp-bench"), r["dir"], r["file"])
        if r["status"] == "sat":
            r["outcome"] = "invalid" if r["outcome"] != "proved" else "proved-invalid"


def _check_forbidden(source):
    hits = [w for w in FORBIDDEN if re.search(r"\b%s\b" % re.escape(w), source)]
    return hits


def _run(cmd, cwd, timeout):
    return subprocess.run(
        cmd,
        cwd=cwd,
        capture_output=True,
        text=True,
        timeout=timeout,
    )


def _parse_csv(path):
    rows = []
    with open(path, newline="") as f:
        for row in csv.DictReader(f):
            rows.append(row)
    return rows


def _evaluate(program_path, stage):
    with open(program_path) as f:
        source = f.read()

    lines = _effective_lines(source)
    hits = _check_forbidden(source)
    if hits:
        return _zero("forbidden constructs: " + ", ".join(hits), lines)

    wt = _worktree()
    if not os.path.isdir(wt):
        return _zero("worktree missing: %s (run evolve/setup_worktree.sh)" % wt)

    target = os.path.join(wt, TARGET)
    shutil.copyfile(program_path, target)

    try:
        build = _run(["lake", "build", "bench"], wt, BUILD_TIMEOUT_S)
    except subprocess.TimeoutExpired:
        return _zero("timeout", lines, timeout="lake build exceeded %ds" % BUILD_TIMEOUT_S)
    if build.returncode != 0:
        out = (build.stdout or "") + "\n" + (build.stderr or "")
        errs = "\n".join(l for l in out.splitlines() if "error" in l or l.startswith("  "))
        return _zero("build failed", lines, build_errors=(errs or out)[-8000:])

    fd, csv_path = tempfile.mkstemp(suffix=".csv")
    os.close(fd)
    cmd = ["lake", "exe", "bench", "--timeout", str(BENCH_TIMEOUT_MS), "--csv", csv_path]
    dirs = STAGE1_DIRS if stage == "stage1" else STAGE2_DIRS
    for d in dirs:
        cmd = cmd[:3] + ["--dir", d] + cmd[3:]
    run_timeout = STAGE1_RUN_TIMEOUT_S if stage == "stage1" else FULL_RUN_TIMEOUT_S

    try:
        proc = _run(cmd, wt, run_timeout)
    except subprocess.TimeoutExpired:
        os.unlink(csv_path)
        return _zero("timeout", lines, timeout="lake exe bench exceeded %ds" % run_timeout)

    if not os.path.exists(csv_path) or os.path.getsize(csv_path) == 0:
        tail = (proc.stderr or proc.stdout or "")[-6000:]
        os.path.exists(csv_path) and os.unlink(csv_path)
        return _zero("bench produced no csv", lines, bench_stderr=tail)

    rows = _parse_csv(csv_path)
    if not rows:
        os.unlink(csv_path)
        return _zero("bench produced an empty csv", lines)
    _label(rows, wt)
    tag = hashlib.sha1(source.encode()).hexdigest()[:8]
    csv_name = "bench-%s.csv" % tag
    with open(os.path.join(wt, csv_name), "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)
    os.unlink(csv_path)

    provable = [r for r in rows if r["status"] != "sat"]
    edge = [r for r in provable if r["outcome"] == "proved" and ms_of(r) > EDGE_MS]
    for r in provable:
        if r["outcome"] == "proved" and ms_of(r) > PROVED_MARGIN_MS:
            r["outcome"] = "proved-no-margin"
    invalid = [r for r in rows if r["status"] == "sat"]
    n = len(provable)
    if n == 0:
        return _zero("no provable problems in the selection", lines)
    _, proved, timeouts, total_ms, worst = totals(provable, BENCH_TIMEOUT_MS)
    _, wrong, _, invalid_ms, invalid_worst = totals(invalid, BENCH_TIMEOUT_MS)
    if wrong:
        return _zero("proved an invalid entailment: encoding bug", lines, wrong=str(wrong))

    proved_fraction = proved / n
    time_score = total_ms / float(n * BENCH_TIMEOUT_MS)
    invalid_time_score = invalid_ms / float(invalid_worst) if invalid_worst else 0.0
    combined = max(0.0, proved_fraction - TIME_WEIGHT * time_score
                   - LINE_WEIGHT * lines - INVALID_TIME_WEIGHT * invalid_time_score)

    feats = scan(os.path.join(wt, "sl-comp-bench"), sorted(set(r["dir"] for r in rows)))
    outcomes = {(r["dir"], r["file"]): r["outcome"] for r in rows}
    artifacts = {
        "totals": _score_table(stage, proved, n, timeouts, total_ms, len(invalid), invalid_ms,
                               invalid_worst, lines, proved_fraction, time_score,
                               invalid_time_score, combined, csv_name),
        "per_directory": dir_summary(rows),
        "features": feature_report(feats, outcomes),
        "failure_shapes": reason_groups(provable) or "(none)",
        "slowest_proved": slowest_proved(rows) or "(none)",
        "near_edge": " ".join("%s=%dms" % (r["file"], ms_of(r)) for r in edge) or "(none)",
        "outcomes": outcome_table(rows),
    }

    metrics = {
        "combined_score": combined,
        "proved": float(proved),
        "n": float(n),
        "total_ms": float(total_ms),
        "proved_fraction": proved_fraction,
        "time_score": time_score,
        "lines": float(lines),
        "invalid_time_score": invalid_time_score,
    }
    return EvaluationResult(metrics=metrics, artifacts=artifacts)


def evaluate_stage1(program_path):
    return _evaluate(program_path, "stage1")


def evaluate_stage2(program_path):
    return _evaluate(program_path, "full")


def evaluate(program_path):
    return _evaluate(program_path, "full")
