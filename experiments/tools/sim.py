"""Synthetic perception pipeline for testing the tool chain.

NOT a model of Autoware and NOT a source of results for the paper. The
pipeline is a chain cloud -> det -> trk -> pred. Every stage reacts to the
messages it actually receives, so a fault injected on a channel propagates
downstream, as it would in the real system.
"""

from __future__ import annotations

import random
from dataclasses import dataclass

from ticks import CHANNELS, Tick

FAULT_CLASSES = ("drop", "delay", "freeze", "range", "confdrop", "objects")

# Which fault classes make sense on which channel.
APPLICABLE = {
    "cloud": ("drop", "delay", "freeze", "range"),
    "det": FAULT_CLASSES,
    "trk": ("drop", "delay", "freeze", "range", "objects"),
    "pred": ("drop", "delay", "freeze", "range"),
}

# The party that produces a channel.
PRODUCER = {"cloud": "environment", "det": "det", "trk": "trk", "pred": "pred"}


@dataclass
class Fault:
    kind: str
    channel: str
    start: int
    end: int  # exclusive
    delay: int = 10


@dataclass
class Msg:
    t: int
    cid: int  # identity of the content; equal cid means equal content
    fields: dict[str, int]


def apply_fault(msgs: list[Msg], channel: str, fault: Fault | None) -> list[Msg]:
    if fault is None or fault.channel != channel:
        return msgs
    inside = lambda m: fault.start <= m.t < fault.end
    if fault.kind == "drop":
        return [m for m in msgs if not inside(m)]
    if fault.kind == "delay":
        out = [Msg(m.t + fault.delay, m.cid, m.fields) if inside(m) else m for m in msgs]
        return sorted(out, key=lambda m: m.t)
    if fault.kind == "freeze":
        before = [m for m in msgs if m.t < fault.start]
        if not before:
            return msgs
        last = before[-1]
        return [Msg(m.t, last.cid, dict(last.fields)) if inside(m) else m for m in msgs]
    out = []
    for m in msgs:
        if inside(m):
            fields = dict(m.fields)
            if fault.kind == "range":
                bad = {"cloud": ("cloud.points", 0), "det": ("det.count", 500),
                       "trk": ("trk.count", 500), "pred": ("pred.maxspeed", 200000)}
                name, value = bad[channel]
                fields[name] = value
            elif fault.kind == "confdrop":
                fields["det.minconf"] = 50
            elif fault.kind == "objects":
                fields[channel + ".count"] = fields[channel + ".count"] + 20
            m = Msg(m.t, m.cid, fields)
        out.append(m)
    return out


def simulate(n_ticks: int, seed: int, fault: Fault | None = None) -> list[Tick]:
    """Return the event file of one run (index 0 is tick 1)."""
    rng = random.Random(seed)

    # Environment: a point cloud every 10 ticks.
    cloud: list[Msg] = []
    count = 5
    for i, t in enumerate(range(1, n_ticks + 1, 10)):
        count = max(0, min(10, count + rng.choice((-1, 0, 1))))
        cloud.append(Msg(t, i, {"cloud.points": 20000 + rng.randint(-500, 500),
                                "_count": count, "_conf": rng.randint(600, 900),
                                "_speed": rng.randint(0, 20000)}))
    cloud = apply_fault(cloud, "cloud", fault)

    # Detection: answers every point cloud after 3 ticks.
    det = []
    for m in cloud:
        degraded = m.fields["cloud.points"] < 1000
        det.append(Msg(m.t + 3, m.cid, {
            "det.count": 0 if degraded else m.fields["_count"],
            "det.minconf": m.fields["_conf"], "_speed": m.fields["_speed"]}))
    det = apply_fault(det, "det", fault)

    # Tracking: answers every detection after 2 ticks.
    trk = [Msg(m.t + 2, m.cid, {"trk.count": m.fields["det.count"],
                                "_speed": m.fields["_speed"]}) for m in det]
    trk = apply_fault(trk, "trk", fault)

    # Prediction: answers every track list after 2 ticks.
    pred = [Msg(m.t + 2, m.cid, {"pred.count": m.fields["trk.count"],
                                 "pred.maxspeed": m.fields["_speed"]}) for m in trk]
    pred = apply_fault(pred, "pred", fault)

    events: list[Tick] = [dict() for _ in range(n_ticks)]
    events[0]["odd"] = 1
    for channel, msgs in zip(CHANNELS, (cloud, det, trk, pred)):
        previous = None
        for m in msgs:
            if not 1 <= m.t <= n_ticks:
                continue
            content = (m.cid, tuple(sorted(m.fields.items())))
            tick = events[m.t - 1]
            tick[channel] = 1
            tick[channel + ".changed"] = int(content != previous)
            tick.update({k: v for k, v in m.fields.items() if not k.startswith("_")})
            previous = content
    return events
