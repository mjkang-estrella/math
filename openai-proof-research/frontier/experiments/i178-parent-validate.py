"""Detached I178 authentication and exclusive read-only parent replay receipts."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "frontier/experiments/i178_five_port_annihilator"
REPORT = ROOT / "frontier/iterations/i178-five-port-annihilator.md"
ANCHORS = {
    REPORT: "77bbc27865e326b5b5e2eebd52f61437683b260feb82c6ed811b14216c2bdc78",
    BASE / "seal.json": "6ae31f2775f1c2af44f47f7637905a104e9981182d4cf5dd656021317988f5f0",
    BASE / "verify178.py": "b000b7c6bfe6c926c2820731bf093d808f177fadfb5909009a131d95be61f531",
}
CONTEXT = {"README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_bytes())


def save(name, value):
    with (BASE.parent / ("i178-parent-"+name+".json")).open("x") as out:
        json.dump(value, out, indent=2, sort_keys=True)
        out.write("\n")


def authenticate():
    for p,h in ANCHORS.items():
        assert sha(p) == h, p
    inv,seal,pre = (read(BASE / n) for n in ("inventory.json","seal.json","prevalidation.json"))
    for name in ("inventory","prevalidation"):
        assert sha(BASE / (name+".json")) == seal[name+"_sha256"]
    assert pre["status"] == "PASS" and pre["prevalidation"]
    for field in ("inventory_sha256","report_sha256","verifier_sha256"):
        assert pre[field] == seal[field]
    assert seal["report_sha256"] == ANCHORS[REPORT]
    assert seal["verifier_sha256"] == ANCHORS[BASE / "verify178.py"]
    controls = {BASE / n for n in ("inventory.json","prevalidation.json","seal.json")}
    assert {ROOT / n for n in inv["controls"]} == controls
    actual = {REPORT}
    for d in (BASE, ROOT / "frontier/sources/i178_five_port_annihilator"):
        actual |= {p for p in d.rglob("*") if p.is_file()}
    assert actual-controls == {ROOT / z["path"] for z in inv["owned"]}
    entries = inv["owned"]+inv["external"]
    assert len(entries) == len({z["path"] for z in entries})
    assert len(inv["context"]) == 4 and {z["path"] for z in inv["context"]} == CONTEXT
    assert not CONTEXT & {z["path"] for z in entries}
    for z in entries:
        p = ROOT / z["path"]
        assert p.resolve().is_relative_to(ROOT) and not p.is_symlink()
        assert sha(p) == z["sha256"] and p.stat().st_size == z["size"], z["path"]
    inputs = read(BASE / "inputs.json")
    assert inputs["strict"] == inv["external"]
    contexts = [dict(path=z["path"],actual=sha(ROOT/z["path"]),
                     inventory=z["sha256"],inherited=z["inherited"]) for z in inv["context"]]
    for replay in inv["replays"]:
        assert any(r["function"] == replay["function"] and r["byte_identical"]
                   and r["sha256"] == sha(ROOT/replay["payload"]) for r in pre["comparisons"])
    assert len(pre["probes"]) == 8 and all(p["blocked"] for p in pre["probes"])
    assert len(inv["owned"]) == 81 and len(inv["external"]) == 678
    return dict(status="PASS",owned=81,non_context_external=678,external_context_total=682,
                contexts=contexts,anchors={str(p.relative_to(ROOT)):h for p,h in ANCHORS.items()})


def main():
    before = authenticate()
    save("precheck",before)
    stdout,stderr = (BASE.parent / ("i178-parent-replay-"+n) for n in ("stdout.json","stderr.txt"))
    with stdout.open("xb") as out, stderr.open("xb") as err:
        run = subprocess.run([sys.executable,"-I","-B",str(BASE/"verify178.py")],
                             cwd=ROOT,stdout=out,stderr=err,timeout=1200)
    assert run.returncode == 0 and not stderr.read_bytes()
    result = read(stdout)
    assert result["status"] == "PASS" and not result["prevalidation"]
    assert result["seal_sha256"] == ANCHORS[BASE/"seal.json"]
    assert len(result["comparisons"]) == 2 and all(z["byte_identical"] for z in result["comparisons"])
    assert len(result["probes"]) == 8 and all(z["blocked"] for z in result["probes"])
    after = authenticate()
    assert before == after
    save("verification",dict(status="PASS",replay=result,postcheck=after,stderr="empty",
         context_policy="Historical drift allowed; current bytes frozen during execution.",
         clean_clone_reconstruction="not tested"))
    print("Parent replay PASS",result["runtime_seconds"],"seconds; 81 owned, 678 external, four contexts")


if __name__ == "__main__":
    main()
