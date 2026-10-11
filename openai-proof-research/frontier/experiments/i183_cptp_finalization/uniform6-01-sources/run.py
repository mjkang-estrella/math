# Adapted from authenticated same-I183 resumed/run.py; finalization scope.
"""Small exclusive-output diagnostic runner; -I -B required."""
import hashlib
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
BASE = Path(__file__).resolve().parent


def module(name):
    path = BASE / name
    ns = {"__file__": str(path), "__name__": "continuation_module"}
    exec(compile(path.read_bytes(), str(path), "exec"), ns)
    return ns


def run(mode):
    auth = module("auth.py")
    before = auth["check"]()
    frozen = auth["load"](auth["BASE"] + "/inputs.json")
    allowed = {x["path"]: x for x in frozen["strict"]}

    def read_json(path):
        assert path in allowed
        data = (ROOT / path).read_bytes()
        assert hashlib.sha256(data).hexdigest() == allowed[path]["sha256"]
        return json.loads(data)

    exact = module("exact.py")
    code = BASE / "geometry.py"
    exec(compile(code.read_bytes(), str(code), "exec"), exact)
    start = time.monotonic()
    if mode == "unit":
        payload = exact["unit_tests"]()
    elif mode == "indexed":
        code = BASE / "indexed.py"
        exec(compile(code.read_bytes(), str(code), "exec"), exact)
        payload = exact["indexed"](read_json)
    elif mode == "incidences":
        code = BASE / "incidences.py"
        exec(compile(code.read_bytes(), str(code), "exec"), exact)
        payload = exact["incidence_tests"]()
    elif mode == "proof":
        code = BASE / "proof_checks.py"
        exec(compile(code.read_bytes(), str(code), "exec"), exact)
        payload = exact["proof_checks"]()
    elif mode in ("calibration", "uniform6"):
        for name in ("indexed.py", "stages.py"):
            code = BASE / name
            exec(compile(code.read_bytes(), str(code), "exec"), exact)
        payload = exact[mode](read_json)
    else:
        raise ValueError(mode)
    runtime = time.monotonic() - start
    assert auth["check"]() == before
    return payload, runtime


if __name__ == "__main__":
    assert sys.flags.isolated and sys.dont_write_bytecode
    mode, name = sys.argv[1:]
    assert Path(name).name == name and name.endswith(".json")
    payload, runtime = run(mode)
    with (BASE / name).open("x") as f:
        json.dump(payload, f, indent=2, sort_keys=True)
        f.write("\n")
    print(json.dumps({"status": payload["status"], "mode": mode,
                      "runtime_seconds": runtime, "output": name},
                     sort_keys=True))
