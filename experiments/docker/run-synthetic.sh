#!/usr/bin/env bash
# Build the monitor and run the synthetic fault-injection campaign.
set -euo pipefail
(cd lean && lake build monitor)
python3 experiments/run.py --monitor lean/.lake/build/bin/monitor \
  --params experiments/configs/params.default --out experiments/results
