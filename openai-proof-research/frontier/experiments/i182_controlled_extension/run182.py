"""Run one fresh I182 diagnostic against frozen authenticated inputs."""
from pathlib import Path
import hashlib
import json
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
BASE = Path(__file__).resolve().parent
STRICT = None


def read_json(relative):
    global STRICT
    if STRICT is None:
        frozen = json.loads((BASE / "inputs.json").read_bytes())
        STRICT = {r["path"]: r for r in frozen["strict"]}
    if not isinstance(relative, str) or relative.startswith("/") or \
            ".." in relative.split("/"):
        raise AssertionError("unbound read")
    if relative not in STRICT:
        raise AssertionError("unbound read: " + relative)
    data = (ROOT / relative).read_bytes()
    row = STRICT[relative]
    assert len(data) == row["size"] and hashlib.sha256(data).hexdigest() == row["sha256"]
    return json.loads(data)


def namespace():
    env = {"__name__": "i182_math"}
    data = (BASE / "math182.py").read_bytes()
    exec(compile(data, str(BASE / "math182.py"), "exec"), env)
    env = dict(env)
    env["read_json"] = read_json
    data = (BASE / "research182.py").read_bytes()
    exec(compile(data, str(BASE / "research182.py"), "exec"), env)
    return env


def main():
    if len(sys.argv) != 3 or sys.argv[1] not in ("mandatory", "extension"):
        raise AssertionError("usage: run182.py mandatory|extension OUTPUT")
    start = time.perf_counter()
    result = namespace()[sys.argv[1]]()
    result["runtime_seconds"] = time.perf_counter() - start
    target = (BASE / sys.argv[2]).resolve()
    if target.exists() or target.parent != BASE:
        raise AssertionError("exclusive output")
    with target.open("x") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"status": result.get("status"),
                      "seconds": result["runtime_seconds"]}))


if __name__ == "__main__":
    main()
