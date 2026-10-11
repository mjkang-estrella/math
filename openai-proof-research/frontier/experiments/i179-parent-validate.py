"""Detached I179 authentication and exclusive parent replay receipts."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT/"frontier/experiments/i179_path_recombination"
REPORT = ROOT/"frontier/iterations/i179-path-recombination.md"
ANCHORS = {
    REPORT: "de1b82735be4839890d6ce76f646db237822da617d6c33ae8564187b17390f12",
    BASE/"seal.json": "b73cf2bee6ec06003a85c7741cc29164b23949b6fe815413c8420e6f3a57d366",
    BASE/"verify179.py": "8ebcb120ed0762c4e7d75e7500833d36dd3c8d4f050784f3c1217de1fe099593",
}
CONTEXT = {"README.md","frontier/README.md","frontier/TEN-FINDINGS.md","frontier/iterations/README.md"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_bytes())


def save(name, value):
    with (BASE.parent/("i179-parent-"+name+".json")).open("x") as out:
        json.dump(value,out,indent=2,sort_keys=True)
        out.write("\n")


def authenticate():
    for p,h in ANCHORS.items():
        assert sha(p) == h,p
    inv,seal,pre = (read(BASE/n) for n in ("inventory.json","seal.json","prevalidation.json"))
    assert pre["status"] == "PASS" and pre["prevalidation"]
    for name in ("inventory","prevalidation"):
        assert sha(BASE/(name+".json")) == seal[name+"_sha256"]
    for field in ("inventory_sha256","report_sha256","verifier_sha256"):
        assert pre[field] == seal[field]
    assert seal["report_sha256"] == ANCHORS[REPORT]
    assert seal["verifier_sha256"] == ANCHORS[BASE/"verify179.py"]
    controls = {BASE/n for n in ("inventory.json","prevalidation.json","seal.json")}
    assert {ROOT/n for n in inv["controls"]} == controls
    actual = {REPORT}
    for d in (BASE,ROOT/"frontier/sources/i179_path_recombination"):
        actual |= {p for p in d.rglob("*") if p.is_file()}
    assert actual-controls == {ROOT/z["path"] for z in inv["owned"]}
    entries = inv["owned"]+inv["external"]
    assert len(entries) == len({z["path"] for z in entries})
    assert len(inv["context"]) == 4 and {z["path"] for z in inv["context"]} == CONTEXT
    assert not CONTEXT & {z["path"] for z in entries}
    for z in entries:
        p = ROOT/z["path"]
        assert p.resolve().is_relative_to(ROOT) and not p.is_symlink()
        assert sha(p) == z["sha256"] and p.stat().st_size == z["size"],p
    first,extra = read(BASE/"inputs.json"),read(BASE/"supplement.json")
    assert len(first["strict"]) == 773 and len(extra["strict"]) == 1
    assert extra["original_inputs_sha256"] == sha(BASE/"inputs.json")
    assert inv["external"] == sorted(first["strict"]+extra["strict"],key=lambda z:z["path"])
    assert extra["strict"][0]["path"] == "frontier/experiments/i178-parent-integration.json"
    contexts = [dict(path=z["path"],actual=sha(ROOT/z["path"]),inventory=z["sha256"],
                     inherited=z["inherited"]) for z in inv["context"]]
    for replay in inv["replays"]:
        assert any(r["function"] == replay["function"] and r["byte_identical"]
                   and r["sha256"] == sha(ROOT/replay["payload"]) for r in pre["comparisons"])
    assert len(pre["probes"]) == 8 and all(p["blocked"] for p in pre["probes"])
    assert len(inv["owned"]) == 122 and len(inv["external"]) == 774
    return dict(status="PASS",owned=122,non_context_external=774,external_context_total=778,
                contexts=contexts,anchors={str(p.relative_to(ROOT)):h for p,h in ANCHORS.items()},
                immutable_freeze="773 original strict paths plus one additive parent-receipt supplement")


def main():
    before = authenticate()
    save("precheck",before)
    stdout,stderr = (BASE.parent/("i179-parent-replay-"+n) for n in ("stdout.json","stderr.txt"))
    with stdout.open("xb") as out,stderr.open("xb") as err:
        run = subprocess.run([sys.executable,"-I","-B",str(BASE/"verify179.py")],
                             cwd=ROOT,stdout=out,stderr=err,timeout=1200)
    assert run.returncode == 0 and not stderr.read_bytes()
    result = read(stdout)
    assert result["status"] == "PASS" and not result["prevalidation"]
    assert result["seal_sha256"] == ANCHORS[BASE/"seal.json"]
    assert len(result["comparisons"]) == 3 and all(z["byte_identical"] for z in result["comparisons"])
    assert len(result["probes"]) == 8 and all(z["blocked"] for z in result["probes"])
    assert before == authenticate()
    save("verification",dict(status="PASS",replay=result,postcheck=before,stderr="empty",
         context_policy="Historical drift allowed; current bytes fixed during execution.",
         clean_clone_reconstruction="not tested"))
    print("Parent replay PASS",result["runtime_seconds"],"seconds; 122 owned, 774 strict external, four contexts")


if __name__ == "__main__":
    main()
