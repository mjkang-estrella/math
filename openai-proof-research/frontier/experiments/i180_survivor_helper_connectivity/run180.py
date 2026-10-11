"""Preserve every mathematical attempt, including exact source stages."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time
import types

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def module(name, payload=None):
    path = HERE / (name + ".py")
    data = path.read_bytes() if payload is None else payload
    obj = types.ModuleType(name)
    obj.__file__ = str(path)
    sys.modules[name] = obj
    exec(compile(data, str(path), "exec"), obj.__dict__)
    return obj


def calculate(name):
    auth = module("auth180")
    freeze = auth.frozen()
    data = {entry["path"]: (ROOT / entry["path"]).read_bytes() for entry in freeze["strict"]}
    for entry in freeze["strict"]:
        assert hashlib.sha256(data[entry["path"]]).hexdigest() == entry["sha256"]
    module("math180")
    research = module("research180")
    result = getattr(research, name)(lambda p: json.loads(data[p]))
    auth.frozen()
    sys.stdout.buffer.write(auth.encoded(result))


def attempt(name):
    auth = module("auth180")
    freeze = auth.frozen()
    number = 1
    while (HERE / (name + "-attempt-%02d-receipt.json" % number)).exists():
        number += 1
    stem = name + "-attempt-%02d" % number
    assert not (HERE / (stem + ".json")).exists()
    auth.exclusive(HERE / (stem + "-preflight.json"), auth.encoded({
        "status": "PASS", "strict": len(freeze["strict"]), "contexts": len(freeze["context"]),
        "inputs_sha256": hashlib.sha256((HERE / "inputs.json").read_bytes()).hexdigest(),
        "before_diagnostics": True}))
    for source in ("auth180.py", "math180.py", "research180.py", "run180.py"):
        auth.exclusive(HERE / (stem + "-" + source + ".disabled"), (HERE / source).read_bytes())
    start = time.monotonic()
    with (HERE / (stem + ".json")).open("xb") as stdout, (
            HERE / (stem + "-stderr.txt")).open("xb") as stderr:
        result = subprocess.run([sys.executable, "-I", "-B", str(HERE / "run180.py"), "--compute", name],
                                stdout=stdout, stderr=stderr, check=False)
    receipt = {"returncode": result.returncode, "seconds": time.monotonic() - start,
               "payload_sha256": hashlib.sha256((HERE / (stem + ".json")).read_bytes()).hexdigest(),
               "stderr_bytes": (HERE / (stem + "-stderr.txt")).stat().st_size}
    auth.frozen()
    receipt["strict_context_before_after"] = "unchanged"
    auth.exclusive(HERE / (stem + "-receipt.json"), auth.encoded(receipt))
    print(json.dumps(dict(receipt, stem=stem)))
    return result.returncode


if __name__ == "__main__":
    assert len(sys.argv) == 3
    assert sys.argv[2] in ("mandatory", "calibration")
    if sys.argv[1] == "--compute":
        calculate(sys.argv[2])
    else:
        assert sys.argv[1] == "--attempt"
        raise SystemExit(attempt(sys.argv[2]))
