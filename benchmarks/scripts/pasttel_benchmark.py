#!/usr/bin/env python3
"""
Runs the Ultimate CLI (BuchiAutomizer, PaSTTeL backend) over every .c file in a
benchmark directory and reports, per lasso check, whether PaSTTeL concluded
(with its ranking function / technique) or delegated to LassoRanker (and why).

Usage:
    python3 pasttel_benchmark.py [--dir benchmarks/C] [--pattern '*.c'] [--limit N]
                                  [--timeout 120] [--out benchmarks/pasttel_dump/report]
                                  [--jobs 1]

Reads PaSTTeL-related log lines directly out of LassoCheck.java's own logging
(tryPasttelTermination/tryPasttelNonTermination/runPasttel/resolvePasttelLasso),
so if those messages change, update the regexes below accordingly.
"""
import argparse
import concurrent.futures
import glob
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DEFAULT_CLI = os.path.join(
    ROOT, "trunk/source/BA_SiteRepository/target/products/CLI-E4/linux/gtk/x86_64/Ultimate")
DEFAULT_TOOLCHAIN = os.path.join(ROOT, "trunk/examples/toolchains/BuchiAutomizerC.xml")
DEFAULT_BASE_SETTINGS = os.path.join(ROOT, "trunk/examples/settings/webinterface/BuchiAutomizerPasttel.epf")
DEFAULT_C_DIR = os.path.join(ROOT, "benchmarks/C")
DEFAULT_OUT_BASE = os.path.join(ROOT, "benchmarks/pasttel_dump")

ITERATION_RE = re.compile(r"={4,}\s*Iteration\s+(\d+)")

# One entry per distinct log message shape emitted by LassoCheck.java.
EVENT_PATTERNS = [
    ("nonterm_no_result", "nonterminate",
     re.compile(r"PaSTTeL non-termination check: no usable result, falling back to LassoRanker")),
    ("nonterm_bad_status", "nonterminate",
     re.compile(r"PaSTTeL non-termination check: (?P<status>\w+), falling back to LassoRanker")),
    ("nonterm_mapping_failed", "nonterminate",
     re.compile(r"PaSTTeL reported NON_TERMINATING but its certificate could not be mapped back "
                r"\(technique=(?P<technique>.*?)\); falling back to LassoRanker")),
    ("nonterm_success", "nonterminate",
     re.compile(r"PaSTTeL non-termination check: SUCCESS via (?P<technique>.+)$")),
    ("term_no_result", "terminate",
     re.compile(r"PaSTTeL termination check: no usable result, falling back to LassoRanker")),
    ("term_bad_status", "terminate",
     re.compile(r"PaSTTeL termination check: (?P<status>\w+), falling back to LassoRanker")),
    ("term_mapping_failed", "terminate",
     re.compile(r"PaSTTeL reported TERMINATING but its certificate could not be mapped back "
                r"\(technique=(?P<technique>.*?)\); falling back to LassoRanker")),
    ("term_success", "terminate",
     re.compile(r"PaSTTeL termination check: SUCCESS via (?P<technique>.+?), ranking function (?P<rf>.+)$")),
    ("invocation_failed", None,
     re.compile(r"PaSTTeL invocation failed, falling back to LassoRanker: (?P<msg>.*)")),
    ("multi_lasso", None,
     re.compile(r"PaSTTeL needs exactly one preprocessed Lasso, got (?P<n>\d+); falling back to LassoRanker")),
]

RESULT_RE = re.compile(r"^RESULT:\s*(.*)$")

DELEGATED_KINDS = {
    "nonterm_no_result", "nonterm_bad_status", "nonterm_mapping_failed",
    "term_no_result", "term_bad_status", "term_mapping_failed",
    "invocation_failed", "multi_lasso",
}
SUCCESS_KINDS = {"nonterm_success", "term_success"}


def parse_log(log_text):
    """Returns (events, results) where events is a list of dicts and results is a list of RESULT: lines."""
    events = []
    results = []
    iteration = 0
    for line in log_text.splitlines():
        m = ITERATION_RE.search(line)
        if m:
            iteration = int(m.group(1))
            continue
        m = RESULT_RE.search(line)
        if m:
            results.append(m.group(1).strip())
            continue
        for kind, mode, pattern in EVENT_PATTERNS:
            m = pattern.search(line)
            if m:
                events.append({
                    "iteration": iteration,
                    "kind": kind,
                    "mode": mode,
                    "outcome": "success" if kind in SUCCESS_KINDS else "delegated",
                    **m.groupdict(),
                })
                break
    return events, results


def run_one(cli, toolchain, base_settings_text, c_file, out_base, timeout):
    stem = os.path.splitext(os.path.basename(c_file))[0]
    dump_dir = os.path.join(out_base, stem)
    os.makedirs(dump_dir, exist_ok=True)
    logs_dir = os.path.join(out_base, "logs")
    os.makedirs(logs_dir, exist_ok=True)

    # Point the dump directory at a per-program subdirectory so concurrent/sequential runs
    # across different .c files can never collide on the same dump file names.
    settings_text = re.sub(
        r"(/instance/de\.uni_freiburg\.informatik\.ultimate\.plugins\.generator\.buchiautomizer/To\\ the\\ following\\ directory=).*",
        r"\g<1>" + dump_dir.replace("\\", "\\\\"),
        base_settings_text,
    )
    settings_path = os.path.join(dump_dir, "settings.epf")
    with open(settings_path, "w") as f:
        f.write(settings_text)

    cmd = [cli, "-tc", toolchain, "-i", c_file, "-s", settings_path]
    start = time.time()
    timed_out = False
    # Own process group: the Ultimate launcher starts a separate JVM (which starts
    # PaSTTeL); on timeout the whole group is killed, not only the launcher.
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            text=True, start_new_session=True)
    try:
        out, err = proc.communicate(timeout=timeout)
        returncode = proc.returncode
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(proc.pid, signal.SIGKILL)
        out, err = proc.communicate()
        returncode = None
    log_text = (out or "") + "\n" + (err or "")
    elapsed = time.time() - start

    log_path = os.path.join(logs_dir, stem + ".log")
    with open(log_path, "w") as f:
        f.write(log_text)

    events, results = parse_log(log_text)
    return {
        "file": os.path.basename(c_file),
        "elapsed_s": round(elapsed, 1),
        "timed_out": timed_out,
        "returncode": returncode,
        "events": events,
        "results": results,
        "log_path": os.path.relpath(log_path, ROOT),
        "dump_dir": os.path.relpath(dump_dir, ROOT),
    }


def format_report_md(runs, args):
    lines = []
    lines.append("# PaSTTeL benchmark report — %s" % time.strftime("%Y-%m-%d %H:%M:%S"))
    lines.append("")
    lines.append("- Directory: `%s`" % os.path.relpath(args.dir, ROOT))
    lines.append("- Toolchain: `%s`" % os.path.relpath(args.toolchain, ROOT))
    lines.append("- Base settings: `%s`" % os.path.relpath(args.settings, ROOT))
    lines.append("- Per-file timeout: %ss" % args.timeout)
    lines.append("- Files processed: %d" % len(runs))
    lines.append("")

    total_events = sum(len(r["events"]) for r in runs)
    by_kind = {}
    techniques = {}
    for r in runs:
        for ev in r["events"]:
            by_kind[ev["kind"]] = by_kind.get(ev["kind"], 0) + 1
            if ev["outcome"] == "success":
                techniques[ev["technique"]] = techniques.get(ev["technique"], 0) + 1

    n_success = sum(v for k, v in by_kind.items() if k in SUCCESS_KINDS)
    n_delegated = sum(v for k, v in by_kind.items() if k in DELEGATED_KINDS)
    timeouts = sum(1 for r in runs if r["timed_out"])

    lines.append("## Global summary")
    lines.append("")
    lines.append("- Total PaSTTeL calls observed: %d" % total_events)
    lines.append("- PaSTTeL concluded (success): %d" % n_success)
    lines.append("- Delegated to LassoRanker: %d" % n_delegated)
    lines.append("- Whole-run timeouts (> %ss wall clock): %d" % (args.timeout, timeouts))
    lines.append("")
    lines.append("### Breakdown by event kind")
    lines.append("")
    lines.append("| kind | count |")
    lines.append("|---|---|")
    for kind, _mode, _pat in EVENT_PATTERNS:
        if by_kind.get(kind):
            lines.append("| %s | %d |" % (kind, by_kind[kind]))
    lines.append("")
    if techniques:
        lines.append("### Successful techniques")
        lines.append("")
        lines.append("| technique | count |")
        lines.append("|---|---|")
        for tech, cnt in sorted(techniques.items(), key=lambda kv: -kv[1]):
            lines.append("| %s | %d |" % (tech, cnt))
        lines.append("")

    lines.append("## Per-file detail")
    lines.append("")
    for r in runs:
        lines.append("### %s" % r["file"])
        lines.append("")
        lines.append("- elapsed: %ss%s, returncode: %s" % (
            r["elapsed_s"], " (TIMEOUT)" if r["timed_out"] else "", r["returncode"]))
        if r["results"]:
            lines.append("- Ultimate verdict: %s" % "; ".join(r["results"]))
        if not r["events"]:
            lines.append("- no PaSTTeL calls observed")
        else:
            lines.append("")
            lines.append("| iteration | mode | outcome | detail |")
            lines.append("|---|---|---|---|")
            for ev in r["events"]:
                if ev["kind"] == "term_success":
                    detail = "SUCCESS via %s — RF: `%s`" % (ev["technique"], ev["rf"])
                elif ev["kind"] == "nonterm_success":
                    detail = "SUCCESS via %s" % ev["technique"]
                elif ev["kind"] in ("term_mapping_failed", "nonterm_mapping_failed"):
                    detail = "certificate could not be mapped back (technique=%s)" % ev["technique"]
                elif ev["kind"] in ("term_bad_status", "nonterm_bad_status"):
                    detail = "status=%s" % ev["status"]
                elif ev["kind"] == "invocation_failed":
                    detail = "invocation failed: %s" % ev["msg"]
                elif ev["kind"] == "multi_lasso":
                    detail = "got %s preprocessed lassos (need exactly 1)" % ev["n"]
                else:
                    detail = "no usable result"
                lines.append("| %d | %s | %s | %s |" % (
                    ev["iteration"], ev["mode"] or "-", ev["outcome"], detail))
        lines.append("")
        lines.append("- raw log: `%s`" % r["log_path"])
        lines.append("- dumped PaSTTeL JSON: `%s`" % r["dump_dir"])
        lines.append("")
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--dir", default=DEFAULT_C_DIR)
    ap.add_argument("--pattern", default="*.c")
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--timeout", type=int, default=120, help="per-file wall-clock timeout in seconds")
    ap.add_argument("--out", default=os.path.join(DEFAULT_OUT_BASE, "report"))
    ap.add_argument("--jobs", type=int, default=1)
    ap.add_argument("--cli", default=DEFAULT_CLI)
    ap.add_argument("--toolchain", default=DEFAULT_TOOLCHAIN)
    ap.add_argument("--settings", default=DEFAULT_BASE_SETTINGS)
    args = ap.parse_args()

    if not os.path.isfile(args.cli) or not os.access(args.cli, os.X_OK):
        sys.exit("Ultimate CLI not found or not executable: %s" % args.cli)

    files = sorted(glob.glob(os.path.join(args.dir, args.pattern)))
    if args.limit:
        files = files[:args.limit]
    if not files:
        sys.exit("No files matched %s in %s" % (args.pattern, args.dir))

    with open(args.settings) as f:
        base_settings_text = f.read()

    out_base = os.path.dirname(args.out) or DEFAULT_OUT_BASE
    os.makedirs(out_base, exist_ok=True)

    print("Running %d files (timeout=%ss, jobs=%d) ..." % (len(files), args.timeout, args.jobs))
    runs = []
    if args.jobs <= 1:
        for i, c_file in enumerate(files, 1):
            print("[%d/%d] %s" % (i, len(files), os.path.basename(c_file)), flush=True)
            runs.append(run_one(args.cli, args.toolchain, base_settings_text, c_file, out_base, args.timeout))
    else:
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
            futs = {ex.submit(run_one, args.cli, args.toolchain, base_settings_text, c_file,
                               out_base, args.timeout): c_file for c_file in files}
            for i, fut in enumerate(concurrent.futures.as_completed(futs), 1):
                c_file = futs[fut]
                print("[%d/%d done] %s" % (i, len(files), os.path.basename(c_file)), flush=True)
                runs.append(fut.result())
        runs.sort(key=lambda r: r["file"])

    md_path = args.out + ".md"
    json_path = args.out + ".json"
    with open(md_path, "w") as f:
        f.write(format_report_md(runs, args))
    with open(json_path, "w") as f:
        json.dump(runs, f, indent=2)

    print("\nReport written to:")
    print("  %s" % md_path)
    print("  %s" % json_path)


if __name__ == "__main__":
    main()
