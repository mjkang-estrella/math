"""Run one fresh I181 diagnostic against frozen authenticated inputs."""
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
        data = (BASE / "inputs.json").read_bytes()
        frozen = json.loads(data)
        STRICT = {r["path"]: r for r in frozen["strict"]}
    if not isinstance(relative, str) or relative.startswith("/") or ".." in relative.split("/"):
        raise AssertionError("unbound read")
    if relative not in STRICT:
        raise AssertionError("unbound read: " + relative)
    data = (ROOT / relative).read_bytes()
    row = STRICT[relative]
    assert len(data) == row["size"] and hashlib.sha256(data).hexdigest() == row["sha256"]
    return json.loads(data)


def namespace():
    ns = {"__name__": "i181_math"}
    for name in ("math181.py", "research181.py"):
        source = (BASE / name).read_bytes()
        code = compile(source, str(BASE / name), "exec")
        exec(code, ns)
        if name == "math181.py":
            math_ns = dict(ns)
    ns = math_ns
    ns["read_json"] = read_json
    source = (BASE / "research181.py").read_bytes()
    exec(compile(source, str(BASE / "research181.py"), "exec"), ns)
    return ns


def main():
    if len(sys.argv) != 3 or sys.argv[1] not in ("mandatory", "topology"):
        raise AssertionError("usage: run181.py mandatory|topology OUTPUT")
    start = time.perf_counter()
    result = namespace()[sys.argv[1]]()
    result["runtime_seconds"] = time.perf_counter() - start
    target = (BASE / sys.argv[2]).resolve()
    if target.exists() or target.parent != BASE:
        raise AssertionError("exclusive output")
    with target.open("x") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"status": result.get("status"), "seconds": result["runtime_seconds"]}))


if __name__ == "__main__":
    main()
