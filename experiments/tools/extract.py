"""Turn a rosbag2 recording of the perception pipeline into an event file.

UNTESTED: written without access to a recording. The topic names, message
field names, and the handling of message definitions must be checked against
a real bag before any result is taken from it.

    python3 experiments/tools/extract.py BAG --config experiments/configs/autoware.json --out run.events

Requires the pure-Python package `rosbags` (no ROS installation).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path

from ticks import Tick, write_ticks


def register_types(typestore, msg_dir: str | None) -> None:
    """Register message definitions that the bag does not embed."""
    if not msg_dir:
        return
    from rosbags.typesys import get_types_from_msg

    types = {}
    for path in Path(msg_dir).rglob("*.msg"):
        # .../<package>/msg/<Name>.msg -> <package>/msg/<Name>
        name = f"{path.parent.parent.name}/msg/{path.stem}"
        types.update(get_types_from_msg(path.read_text(), name))
    typestore.register(types)


def digest(*parts) -> int:
    return int(hashlib.sha1(repr(parts).encode()).hexdigest()[:12], 16)


def cloud_fields(msg) -> tuple[dict[str, int], int]:
    points = int(msg.width) * int(msg.height)
    return {"cloud.points": points}, digest(points, bytes(msg.data[:4096]))


def object_positions(objects, pose_of) -> list[tuple[float, float]]:
    out = []
    for o in objects:
        p = pose_of(o).pose.position
        out.append((round(p.x, 2), round(p.y, 2)))
    return sorted(out)


def det_fields(msg) -> tuple[dict[str, int], int]:
    objs = msg.objects
    conf = min((o.existence_probability for o in objs), default=1.0)
    pos = object_positions(objs, lambda o: o.kinematics.pose_with_covariance)
    return {"det.count": len(objs), "det.minconf": int(round(conf * 1000))}, digest(pos)


def trk_fields(msg) -> tuple[dict[str, int], int]:
    objs = msg.objects
    pos = object_positions(objs, lambda o: o.kinematics.pose_with_covariance)
    return {"trk.count": len(objs)}, digest(pos)


def pred_fields(msg) -> tuple[dict[str, int], int]:
    objs = msg.objects
    speeds = []
    for o in objs:
        v = o.kinematics.initial_twist_with_covariance.twist.linear
        speeds.append(math.sqrt(v.x * v.x + v.y * v.y + v.z * v.z))
    pos = object_positions(objs, lambda o: o.kinematics.initial_pose_with_covariance)
    return ({"pred.count": len(objs), "pred.maxspeed": int(round(max(speeds, default=0.0) * 1000))},
            digest(pos))


EXTRACTORS = {"cloud": cloud_fields, "det": det_fields, "trk": trk_fields, "pred": pred_fields}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("bag")
    ap.add_argument("--config", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--msgs", help="directory with .msg files of message packages the bag does not embed")
    args = ap.parse_args()

    from rosbags.highlevel import AnyReader
    from rosbags.typesys import Stores, get_typestore

    config = json.loads(Path(args.config).read_text())
    tick_ns = int(config["tick_ms"]) * 1_000_000
    topic_of = config["topics"]  # channel -> topic
    channel_of = {topic: channel for channel, topic in topic_of.items()}

    typestore = get_typestore(Stores.ROS2_HUMBLE)
    register_types(typestore, args.msgs)

    events: dict[int, Tick] = {}
    previous: dict[str, int] = {}
    t0 = None
    with AnyReader([Path(args.bag)], default_typestore=typestore) as reader:
        connections = [c for c in reader.connections if c.topic in channel_of]
        for connection, timestamp, raw in reader.messages(connections=connections):
            if t0 is None:
                t0 = timestamp
            tick = (timestamp - t0) // tick_ns + 1
            channel = channel_of[connection.topic]
            fields, content = EXTRACTORS[channel](reader.deserialize(raw, connection.msgtype))
            row = events.setdefault(tick, {})
            row[channel] = 1
            row[channel + ".changed"] = int(previous.get(channel) != content)
            row.update(fields)
            previous[channel] = content

    if not events:
        raise SystemExit("no messages on the configured topics")
    n = max(events)
    ticks = [events.get(t, {}) for t in range(1, n + 1)]
    ticks[0].update(config.get("constants", {}))
    write_ticks(args.out, ticks)
    print(f"{n} ticks, {sum(1 for t in ticks if t)} with messages")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
