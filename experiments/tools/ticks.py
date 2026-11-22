"""Tick files: one line per tick, `name=value` pairs separated by blanks.

An *event file* lists, per tick, the signals of the messages that arrived in
that tick. A *latched file* additionally holds the most recent value of every
non-event signal. The monitor reads latched files.
"""

from __future__ import annotations

CHANNELS = ("cloud", "det", "trk", "pred")

# Signals that are present only in the tick a message arrives.
EVENT_SIGNALS = set(CHANNELS) | {c + ".changed" for c in CHANNELS}

Tick = dict[str, int]


def latch(events: list[Tick]) -> list[Tick]:
    """Hold the last value of every non-event signal."""
    held: Tick = {}
    out: list[Tick] = []
    for tick in events:
        for name, value in tick.items():
            if name not in EVENT_SIGNALS:
                held[name] = value
        row = dict(held)
        row.update({n: v for n, v in tick.items() if n in EVENT_SIGNALS})
        out.append(row)
    return out


def format_tick(tick: Tick) -> str:
    return " ".join(f"{name}={value}" for name, value in sorted(tick.items()))


def write_ticks(path: str, ticks: list[Tick]) -> None:
    with open(path, "w") as f:
        for tick in ticks:
            f.write(format_tick(tick) + "\n")


def read_ticks(path: str) -> list[Tick]:
    ticks: list[Tick] = []
    with open(path) as f:
        for line in f:
            tick: Tick = {}
            for token in line.split():
                name, _, value = token.partition("=")
                tick[name] = int(value)
            ticks.append(tick)
    return ticks
