"""One-way I179 packaging: inventory, successful prevalidation, exclusive seal."""
import ast
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
REL = "frontier/experiments/i179_path_recombination/"
REPORT = "frontier/iterations/i179-path-recombination.md"
CONTROL = {REL+n for n in ("inventory.json", "prevalidation.json", "seal.json")}


def digest(b):
    return hashlib.sha256(b).hexdigest()


def encoded(o):
    return (json.dumps(o, indent=2, sort_keys=True)+"\n").encode()


def exclusive(name, data):
    with (HERE / name).open("xb") as f:
        f.write(data)


def record(p):
    b = (ROOT / p).read_bytes()
    return dict(path=p, size=len(b), sha256=digest(b))


def inventory():
    assert not any((ROOT / p).exists() for p in CONTROL)
    inputs = json.loads((HERE / "inputs.json").read_bytes())
    extra = json.loads((HERE / "supplement.json").read_bytes())
    external = sorted(inputs["strict"]+extra["strict"], key=lambda r: r["path"])
    for r in external:
        assert record(r["path"]) == r
    paths = {REPORT}
    for folder in (HERE, ROOT / "frontier/sources/i179_path_recombination"):
        paths.update(str(p.relative_to(ROOT)) for p in folder.rglob("*") if p.is_file())
    checked = dict(python=[], json=[], empty=[], whitespace_warnings=[])
    for p in sorted(paths):
        b = (ROOT / p).read_bytes()
        if not b:
            checked["empty"].append(p)
            continue
        if p.endswith((".py", ".py.disabled")):
            ast.parse(b, filename=p)
            checked["python"].append(p)
        if p.endswith(".json"):
            json.loads(b)
            checked["json"].append(p)
        if p.endswith((".md", ".py", ".json", ".py.disabled")):
            for i, line in enumerate(b.decode().splitlines(), 1):
                if line.rstrip() != line:
                    checked["whitespace_warnings"].append([p, i])
    assert not checked["whitespace_warnings"]
    exclusive("source-validation.json", encoded(checked))
    paths.add(REL+"source-validation.json")
    inv = dict(iteration=179, owned=[record(p) for p in sorted(paths)],
               external=external, context=inputs["context"], controls=sorted(CONTROL),
               policy="Immutable first; only four inherited-context exemptions; current bytes frozen at replay",
               replays=[dict(function=f, payload=REL+p) for f, p in [
                   ("mandatory", "mandatory-attempt-09.json"),
                   ("analytic", "analytic-attempt-03.json"),
                   ("recombination", "recombination-attempt-03.json")]])
    exclusive("inventory.json", encoded(inv))
    print(json.dumps(dict(status="PASS", owned=len(inv["owned"]), external=len(external), contexts=4)))


def prevalidate():
    assert not (HERE / "prevalidation.json").exists() and not (HERE / "seal.json").exists()
    run = subprocess.run([sys.executable, "-I", "-B", str(HERE / "verify179.py"), "--prevalidate"],
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if run.returncode or run.stderr:
        exclusive("failed-prevalidation-stdout.txt", run.stdout)
        exclusive("failed-prevalidation-stderr.txt", run.stderr)
        exclusive("failed-prevalidation-inventory.json", (HERE / "inventory.json").read_bytes())
        raise RuntimeError(run.stderr.decode())
    receipt = json.loads(run.stdout)
    assert receipt["status"] == "PASS" and receipt["prevalidation"] is True
    exclusive("prevalidation.json", run.stdout)
    print(run.stdout.decode(), end="")


def seal():
    pre = json.loads((HERE / "prevalidation.json").read_bytes())
    assert pre["status"] == "PASS"
    assert pre["inventory_sha256"] == digest((HERE / "inventory.json").read_bytes())
    inv = json.loads((HERE / "inventory.json").read_bytes())
    for r in inv["owned"]+inv["external"]:
        assert record(r["path"]) == r
    value = dict(iteration=179, inventory_sha256=pre["inventory_sha256"],
                 prevalidation_sha256=digest((HERE / "prevalidation.json").read_bytes()),
                 report_sha256=record(REPORT)["sha256"],
                 verifier_sha256=record(REL+"verify179.py")["sha256"],
                 policy="Exactly one exclusive seal after successful prevalidation; never reseal.")
    exclusive("seal.json", encoded(value))
    print(json.dumps(value, indent=2))


if __name__ == "__main__":
    {"inventory": inventory, "prevalidate": prevalidate, "seal": seal}[sys.argv[1]]()
