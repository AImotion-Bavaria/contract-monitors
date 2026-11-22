# Stage 1 of the experiment set-up: Lean monitor and Python tools.
# Build from the repository root:
#   docker build -t cm-monitor -f experiments/docker/monitor.Dockerfile .
# Run the synthetic campaign:
#   docker run --rm -v "$PWD":/work cm-monitor bash experiments/docker/run-synthetic.sh
FROM ubuntu:24.04

RUN apt-get update \
 && apt-get install -y --no-install-recommends ca-certificates curl git python3 python3-venv \
 && rm -rf /var/lib/apt/lists/*

# Lean version manager; the toolchain pinned in lean/lean-toolchain is fetched on first build.
RUN curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"

RUN python3 -m venv /opt/venv && /opt/venv/bin/pip install --no-cache-dir rosbags
ENV PATH="/opt/venv/bin:${PATH}"

WORKDIR /work
