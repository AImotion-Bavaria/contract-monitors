# Experiments

Tool chain for the evaluation: tick files, the compiled Lean monitor, fault
injection, and metrics. See `notes/experiment-setup.md` for the overall plan.

## What is here

| Path | Purpose | Status |
|---|---|---|
| `../lean/Main.lean` | executable `monitor`: runs the synthesised monitors of the perception contracts on a tick file | tested |
| `../lean/ContractMonitors/Perception.lean` | contracts of system, detection, tracking, prediction | builds; refinement between component and system contracts not yet proved |
| `tools/ticks.py` | tick file format, latching | tested via the campaign |
| `tools/sim.py` | synthetic pipeline with fault injection that propagates downstream | tested; not a model of Autoware |
| `tools/evaluate.py` | detection, delay, blame attribution | tested via the campaign |
| `run.py` | campaign over fault classes, channels, seeds | tested |
| `tools/extract.py` | rosbag2 to event file | **untested**, written without a recording |
| `docker/monitor.Dockerfile` | container for all of the above | **untested** |

## Run the synthetic campaign

Without Docker (needs Lean via elan and Python 3.10 or later):

    (cd lean && lake build monitor)
    python3 experiments/run.py --monitor lean/.lake/build/bin/monitor --out experiments/results

With Docker:

    docker build -t cm-monitor -f experiments/docker/monitor.Dockerfile .
    docker run --rm -v "$PWD":/work cm-monitor bash experiments/docker/run-synthetic.sh

The campaign prints a table and writes `results/runs.csv`. Its numbers show
that the tools work together. They are not results: the synthetic pipeline
and the contracts were written by the same hand.

## Tick files

One line per tick, `name=value` pairs separated by blanks. Events (`cloud`,
`det`, `trk`, `pred`, `<channel>.changed`) are present only in the tick a
message arrives; all other signals hold the value of the most recent message.
Values are integers: confidence in per mille, speed in mm/s.

    monitor --list                      # name, component, role of every monitor
    monitor --params FILE < run.ticks   # one line per tick: tick, then 1 per alarm
