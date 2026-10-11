"""Development runner. Exclusive attempt files preserve every failure."""
import hashlib
import json
from pathlib import Path
import sys
import time
import traceback
import types

ROOT = Path(__file__).resolve().parents[3]
EXP = ROOT / "frontier/experiments/i173_brace_high_loss_octagons"
SRC = ROOT / "frontier/sources/i173_brace_high_loss_octagons"


def encode(x):
    return (json.dumps(x, sort_keys=True, separators=(",", ":")) + "\n").encode()


def load():
    auth = json.loads((SRC / "authentication.json").read_bytes())
    memory = {}
    for r in auth["bindings"]:
        raw = (ROOT / r["path"]).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == r["sha256"], r["path"]
        memory[r["path"]] = raw
    for name in ("surgeries-attempt-01.json",):
        path = EXP / name
        if path.exists() and path.stat().st_size:
            memory[str(path.relative_to(ROOT))] = path.read_bytes()
    for name in ("toolkit", "research"):
        module = types.ModuleType(name)
        sys.modules[name] = module
        path = EXP / (name + ".py")
        exec(compile(path.read_bytes(), str(path), "exec"), module.__dict__)
    sys.modules["research"].DATA = memory
    return sys.modules["research"]


if __name__ == "__main__":
    name, attempt = sys.argv[1:]
    output = EXP / (name + "-attempt-" + attempt + ".json")
    error = EXP / (name + "-attempt-" + attempt + "-error.txt")
    # Freeze executed source stages before invoking any mathematical code.
    for module in ("toolkit", "research", "run"):
        with (EXP / (name + "-attempt-" + attempt + "-" + module + ".py.disabled")).open("xb") as out:
            out.write((EXP / (module + ".py")).read_bytes())
    start = time.monotonic()
    with output.open("xb") as out, error.open("x") as err:
        try:
            module = load()
            if name != "mandatory":
                assert (EXP / "mandatory-attempt-01.json").stat().st_size > 0
                module.mandatory()
            result = getattr(module, name)()
            out.write(encode(result))
            print(json.dumps(dict(status="PASS", function=name, runtime=time.monotonic() - start)))
        except BaseException:
            traceback.print_exc(file=err)
            raise
