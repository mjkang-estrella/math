"""Read-only structured schema inspection, no historical code execution."""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]


def shape(obj, depth=2):
    if depth == 0:
        return list(obj) if isinstance(obj, dict) else (
            ["length", len(obj), "first", shape(obj[0], 0)] if isinstance(obj, list)
            and obj and isinstance(obj[0], (list, dict)) else obj)
    if isinstance(obj, dict):
        return {k: shape(v, depth-1) for k, v in obj.items()}
    if isinstance(obj, list):
        return {"length": len(obj), "first": shape(obj[0], depth-1) if obj else None}
    return obj


if __name__ == "__main__":
    assert sys.flags.isolated and sys.dont_write_bytecode
    for name in sys.argv[1:]:
        path, *selector = name.split("::")
        obj = json.loads((ROOT / path).read_bytes())
        for key in selector:
            obj = obj[int(key)] if isinstance(obj, list) else obj[key]
        print(name, json.dumps(shape(obj), indent=2))
