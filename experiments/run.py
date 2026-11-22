"""Run a fault-injection campaign on the synthetic pipeline.

This exercises the tool chain end to end: simulate -> latch -> monitor ->
evaluate. The numbers it prints say whether the tools work, nothing about
Autoware.

    python3 experiments/run.py --monitor lean/.lake/build/bin/monitor --out results
"""

from __future__ import annotations

import argparse
import csv
import os
import subprocess
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "tools"))

from evaluate import evaluate, read_specs, read_verdicts  # noqa: E402
from sim import APPLICABLE, PRODUCER, Fault, simulate  # noqa: E402
from ticks import format_tick, latch  # noqa: E402


def run_monitor(monitor: str, ticks: list[dict], params: str | None) -> str:
    cmd = [monitor] + (["--params", params] if params else [])
    text = "".join(format_tick(t) + "\n" for t in ticks)
    return subprocess.run(cmd, input=text, capture_output=True, text=True, check=True).stdout


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--monitor", required=True, help="path to the compiled Lean monitor")
    ap.add_argument("--params", help="file with contract bounds (key=value per line)")
    ap.add_argument("--out", default="results")
    ap.add_argument("--ticks", type=int, default=600)
    ap.add_argument("--seeds", type=int, default=5)
    ap.add_argument("--start", type=int, default=200)
    ap.add_argument("--length", type=int, default=100)
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)

    cmd = [args.monitor, "--list"] + (["--params", args.params] if args.params else [])
    specs = read_specs(subprocess.run(cmd, capture_output=True, text=True, check=True).stdout)

    rows = []
    for seed in range(args.seeds):
        # nominal run: every alarm is a false alarm
        names, verdicts = read_verdicts(
            run_monitor(args.monitor, latch(simulate(args.ticks, seed)), args.params))
        r = evaluate(specs, names, verdicts, None, None)
        rows.append({"seed": seed, "fault": "none", "channel": "", "responsible": "", **r})
        for channel, kinds in APPLICABLE.items():
            for kind in kinds:
                fault = Fault(kind, channel, args.start, args.start + args.length)
                names, verdicts = read_verdicts(run_monitor(
                    args.monitor, latch(simulate(args.ticks, seed, fault)), args.params))
                r = evaluate(specs, names, verdicts, fault.start, PRODUCER[channel])
                rows.append({"seed": seed, "fault": kind, "channel": channel,
                             "responsible": PRODUCER[channel], **r})

    fields = sorted({k for row in rows for k in row}, key=lambda k: (k not in ("seed", "fault", "channel", "responsible"), k))
    with open(os.path.join(args.out, "runs.csv"), "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        w.writerows(rows)

    nominal = [r for r in rows if r["fault"] == "none"]
    faulty = [r for r in rows if r["fault"] != "none"]
    print(f"nominal runs: {len(nominal)}, with alarms: {sum(1 for r in nominal if r['alarms'])}")
    print(f"faulty runs:  {len(faulty)}, detected: {sum(r['detected'] for r in faulty)}")
    print(f"{'channel':8} {'fault':9} {'det':>4} {'delay':>6}  attribution")
    for channel, kinds in APPLICABLE.items():
        for kind in kinds:
            sel = [r for r in faulty if r["channel"] == channel and r["fault"] == kind]
            delays = [r["delay"] for r in sel if r["delay"] is not None]
            mean = f"{sum(delays) / len(delays):.1f}" if delays else "-"
            attr = {}
            for r in sel:
                key = r["attribution"] if r["attribution"] == "correct" else f"{r['attribution']}({r['blamed']})"
                attr[key] = attr.get(key, 0) + 1
            print(f"{channel:8} {kind:9} {sum(r['detected'] for r in sel):>2}/{len(sel)} {mean:>6}  "
                  + ", ".join(f"{k}: {v}" for k, v in sorted(attr.items())))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
