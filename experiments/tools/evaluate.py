"""Evaluate monitor verdicts against an injected fault."""

from __future__ import annotations

import csv
from dataclasses import dataclass


@dataclass
class Spec:
    name: str
    component: str
    role: str


def read_specs(text: str) -> list[Spec]:
    rows = list(csv.DictReader(text.splitlines()))
    return [Spec(r["name"], r["component"], r["role"]) for r in rows]


def read_verdicts(text: str) -> tuple[list[str], list[list[int]]]:
    """Return the monitor names and, per tick, the alarm flags."""
    rows = list(csv.reader(text.splitlines()))
    names = rows[0][1:]
    return names, [[int(c) for c in row[1:]] for row in rows[1:]]


def first_alarms(names: list[str], verdicts: list[list[int]]) -> dict[str, int]:
    """First tick (1-based) at which each monitor raises an alarm."""
    first: dict[str, int] = {}
    for t, row in enumerate(verdicts, start=1):
        for name, alarm in zip(names, row):
            if alarm and name not in first:
                first[name] = t
    return first


def blame(specs: list[Spec], first: dict[str, int]) -> tuple[int | None, set[str]]:
    """Earliest blame event and the parties blamed at that tick.

    A component is blamed at tick t if one of its guarantee monitors raises an
    alarm at t and none of its assumption monitors has raised an alarm up to t
    (Theorem on blame). The environment is blamed when an assumption monitor
    of the system raises an alarm.
    """
    events: list[tuple[int, str]] = []
    components = {s.component for s in specs}
    for c in components:
        a_first = min((first[s.name] for s in specs
                       if s.component == c and s.role == "A" and s.name in first),
                      default=None)
        if c == "system":
            if a_first is not None:
                events.append((a_first, "environment"))
            continue
        g_first = min((first[s.name] for s in specs
                       if s.component == c and s.role == "G" and s.name in first),
                      default=None)
        if g_first is not None and (a_first is None or a_first > g_first):
            events.append((g_first, c))
    if not events:
        return None, set()
    t = min(e[0] for e in events)
    return t, {party for when, party in events if when == t}


def evaluate(specs: list[Spec], names: list[str], verdicts: list[list[int]],
             fault_start: int | None, responsible: str | None) -> dict:
    first = first_alarms(names, verdicts)
    by_name = {s.name: s for s in specs}
    component_alarm = min((t for n, t in first.items()
                           if by_name[n].component != "system"), default=None)
    system_g_alarm = min((t for n, t in first.items()
                          if by_name[n].component == "system" and by_name[n].role == "G"),
                         default=None)
    blame_tick, blamed = blame(specs, first)
    result = {
        "alarms": len(first),
        "first_alarm": min(first.values(), default=None),
        "first_component_alarm": component_alarm,
        "first_system_guarantee_alarm": system_g_alarm,
        "blame_tick": blame_tick,
        "blamed": "+".join(sorted(blamed)),
    }
    if fault_start is not None:
        detected = component_alarm is not None and component_alarm >= fault_start
        result["detected"] = int(detected)
        result["delay"] = component_alarm - fault_start if detected else None
        if not blamed:
            result["attribution"] = "none"
        elif blamed == {responsible}:
            result["attribution"] = "correct"
        elif responsible in blamed:
            result["attribution"] = "ambiguous"
        else:
            result["attribution"] = "wrong"
    return result
