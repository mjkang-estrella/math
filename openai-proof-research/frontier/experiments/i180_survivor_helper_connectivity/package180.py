"""One-way packaging. All writes are exclusive and in the assigned package."""
import ast
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import types

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PREFIX = str(HERE.relative_to(ROOT)) + "/"
REPORT = "frontier/iterations/i180-survivor-helper-connectivity.md"


def exclusive(p, data):
    with p.open("xb") as f:
        f.write(data)


def encoded(x):
    return (json.dumps(x, sort_keys=True, indent=2) + "\n").encode()


def record(p):
    b = (ROOT / p).read_bytes()
    return {"path": p, "size": len(b), "sha256": hashlib.sha256(b).hexdigest()}


def owned():
    files = {REPORT}
    for sub in ("experiments", "sources"):
        for f in (ROOT / ("frontier/" + sub + "/i180_survivor_helper_connectivity")).rglob("*"):
            assert not f.is_symlink()
            if f.is_file():
                files.add(str(f.relative_to(ROOT)))
    return sorted(files)


def source_check():
    checks = {"status": "PASS", "python": [], "json": [], "markdown": [], "links": []}
    for p in owned():
        b = (ROOT / p).read_bytes()
        if p.endswith(".py") or p.endswith(".py.disabled"):
            ast.parse(b, filename=str(ROOT / p))
            checks["python"].append(p)
        if p.endswith(".json") and b:
            json.loads(b)
            checks["json"].append(p)
        if p.endswith((".md", ".py", ".py.disabled")):
            text = b.decode()
            assert all(line == line.rstrip() for line in text.splitlines()), p
            assert text.endswith("\n")
        if p.endswith(".md"):
            checks["markdown"].append(p)
            for target in re.findall(r"\]\(([^)]+)\)", b.decode()):
                if "://" not in target:
                    path = ((ROOT / p).parent / target.split("#")[0]).resolve()
                    assert path.is_file(), (p, target)
                    checks["links"].append([p, target])
    return checks


def package():
    assert sys.flags.isolated and sys.dont_write_bytecode
    assert not any((HERE / f).exists() for f in ("inventory.json", "prevalidation.json", "seal.json"))
    # Owned authentication code only; ancestor files stay opaque bytes.
    module = types.ModuleType("auth180")
    module.__file__ = str(HERE / "auth180.py")
    exec(compile((HERE / "auth180.py").read_bytes(), module.__file__, "exec"), module.__dict__)
    freeze = module.frozen()
    exclusive(HERE / "source-validation.json", encoded(source_check()))
    controls = [PREFIX + p for p in ("inventory.json", "prevalidation.json", "seal.json")]
    inventory = {
        "iteration": 180, "owned": [record(p) for p in owned()],
        "external": freeze["strict"], "context": freeze["context"], "controls": controls,
        "replays": [
            {"function": "mandatory", "payload": PREFIX + "mandatory-attempt-02.json"},
            {"function": "calibration", "payload": PREFIX + "calibration-attempt-02.json"}],
        "policy": "Complete immutable inventory, successful prevalidation, one exclusive seal, read-only replay.",
    }
    exclusive(HERE / "inventory.json", encoded(inventory))
    process = subprocess.run([sys.executable, "-I", "-B", str(HERE / "verify180.py"), "--prevalidate"],
                             capture_output=True, check=False)
    if process.returncode or process.stderr:
        exclusive(HERE / "prevalidation-failed-stdout.json", process.stdout)
        exclusive(HERE / "prevalidation-failed-stderr.txt", process.stderr)
        raise RuntimeError("Prevalidation failed; original inventory and streams preserved; no seal.")
    result = json.loads(process.stdout)
    assert result["status"] == "PASS" and result["prevalidation"]
    exclusive(HERE / "prevalidation.json", process.stdout)
    seal = {
        "iteration": 180,
        "inventory_sha256": record(PREFIX + "inventory.json")["sha256"],
        "prevalidation_sha256": record(PREFIX + "prevalidation.json")["sha256"],
        "report_sha256": record(REPORT)["sha256"],
        "verifier_sha256": record(PREFIX + "verify180.py")["sha256"],
        "policy": "One exclusive seal after successful prevalidation. Never reseal.",
    }
    exclusive(HERE / "seal.json", encoded(seal))
    print(json.dumps({"status": "SEALED", "owned": len(inventory["owned"]),
                      "strict_external": len(inventory["external"]), "contexts": 4,
                      "prevalidation_seconds": result["runtime_seconds"],
                      "seal_sha256": record(PREFIX + "seal.json")["sha256"]}))


if __name__ == "__main__":
    package()
