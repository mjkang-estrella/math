"""Build a complete inventory, prevalidate, then create exactly one seal."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
PREFIX = "frontier/experiments/i174_prism_gadget_survival/"
SOURCE = "frontier/sources/i174_prism_gadget_survival/"
REPORT = "frontier/iterations/i174-prism-gadget-survival.md"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def write(name,obj):
    with (HERE/name).open("x") as f:
        json.dump(obj,f,indent=2,sort_keys=True)
        f.write("\n")


def binding(path):
    data = (ROOT/path).read_bytes()
    return dict(path=path,sha256=sha(data),size=len(data))


def build():
    assert not (HERE/"seal.json").exists()
    controls = [PREFIX+x for x in ("inventory.json","prevalidation.json","seal.json")]
    paths = {REPORT}
    for directory in (HERE,ROOT/SOURCE):
        paths.update(str(p.relative_to(ROOT)) for p in directory.rglob("*") if p.is_file())
    paths -= set(controls)
    auth = json.loads((ROOT/SOURCE/"authentication.json").read_bytes())
    transition = json.loads((ROOT/SOURCE/"parent-disposition-transition.json").read_bytes())
    external = []
    for entry in auth["bindings"]:
        if entry["path"] == transition["path"]:
            assert entry["sha256"] == transition["old_sha256"]
            assert sha((ROOT/transition["old_snapshot"]).read_bytes()) == entry["sha256"]
            current = binding(entry["path"])
            assert current["sha256"] == transition["new_sha256"]
            assert sha((ROOT/transition["new_snapshot"]).read_bytes()) == current["sha256"]
            external.append(current)
        else:
            assert binding(entry["path"]) == entry
            external.append(entry)
    jobs = []
    for name in ("mandatory","certificates","experiments","structural"):
        receipts = sorted(HERE.glob(name+"-attempt-*-receipt.json"))
        passed = [json.loads(p.read_bytes()) for p in receipts if json.loads(p.read_bytes())["status"] == "PASS"]
        assert passed
        jobs.append(dict(function=name,payload=PREFIX+passed[-1]["payload"]))
    inv = dict(iteration=174,owned=[binding(p) for p in sorted(paths)],
               external=external,context=auth["context"],controls=controls,
               replays=jobs,modules=["mathkit","research"],
               policy="All inputs frozen before diagnostics; ancestors opaque; one exclusive seal; no reseal")
    write("inventory.json",inv)
    print(json.dumps(dict(owned=len(inv["owned"]),external=len(inv["external"]),contexts=4,replays=jobs)))


def prevalidate():
    assert not (HERE/"seal.json").exists()
    result = subprocess.run([sys.executable,"-I","-B",str(HERE/"verify.py"),"--prevalidate"],
                            capture_output=True,check=False)
    if result.returncode or result.stderr:
        # A failure is never disguised as successful prevalidation.
        print(result.stdout.decode(),end="")
        print(result.stderr.decode(),file=sys.stderr,end="")
        raise SystemExit(result.returncode or 1)
    receipt = json.loads(result.stdout)
    assert receipt["status"] == "PASS" and receipt["prevalidation"]
    write("prevalidation.json",dict(status="PASS",stderr="",result=receipt))
    print(json.dumps(dict(status="PASS",seconds=receipt["runtime_seconds"])))


def seal():
    pre = json.loads((HERE/"prevalidation.json").read_bytes())
    assert pre["status"] == "PASS" and pre["stderr"] == ""
    assert pre["result"]["inventory_sha256"] == sha((HERE/"inventory.json").read_bytes())
    for group in ("owned","external"):
        for entry in json.loads((HERE/"inventory.json").read_bytes())[group]:
            assert binding(entry["path"]) == entry
    value = dict(iteration=174,creation="exclusive single seal after successful prevalidation; never reseal",
                 inventory_sha256=sha((HERE/"inventory.json").read_bytes()),
                 prevalidation_sha256=sha((HERE/"prevalidation.json").read_bytes()),
                 report_sha256=sha((ROOT/REPORT).read_bytes()),
                 verifier_sha256=sha((HERE/"verify.py").read_bytes()))
    write("seal.json",value)
    print(json.dumps(dict(value,seal_sha256=sha((HERE/"seal.json").read_bytes())),indent=2))


if __name__ == "__main__":
    {"build":build,"prevalidate":prevalidate,"seal":seal}[sys.argv[1]]()
