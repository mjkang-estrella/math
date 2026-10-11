"""Preserve sources and exclusive captures before every local invocation."""
import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
BASE = Path(__file__).resolve().parent


def record(path):
    data = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(), "size": len(data),
            "sha256": hashlib.sha256(data).hexdigest()}


if __name__ == "__main__":
    assert sys.flags.isolated and sys.dont_write_bytecode
    name, script, *args = sys.argv[1:]
    assert Path(name).name == name and Path(script).name == script
    snapshots = BASE / (name + "-sources")
    snapshots.mkdir()
    sources = list(BASE.glob("*.py"))
    for path in sources:
        with (snapshots / path.name).open("xb") as out:
            out.write(path.read_bytes())
    with (BASE / (name + "-invocation.json")).open("x") as out:
        json.dump({"argv": ["python3", "-I", "-B", script, *args],
                   "sources": [record(p) for p in sorted(snapshots.iterdir())]},
                  out, indent=2, sort_keys=True)
        out.write("\n")
    start = time.monotonic()
    with (BASE / (name + ".stdout")).open("xb") as stdout, \
            (BASE / (name + ".stderr")).open("xb") as stderr:
        completed = subprocess.run(
            [sys.executable, "-I", "-B", str(BASE / script), *args],
            cwd=ROOT, stdout=stdout, stderr=stderr, check=False)
    receipt = {"returncode": completed.returncode,
               "seconds": time.monotonic() - start}
    with (BASE / (name + "-receipt.json")).open("x") as out:
        json.dump(receipt, out, sort_keys=True)
        out.write("\n")
    print(json.dumps(receipt, sort_keys=True))
    if completed.returncode:
        print((BASE / (name + ".stderr")).read_text())
    else:
        print((BASE / (name + ".stdout")).read_text())
    sys.exit(completed.returncode)
