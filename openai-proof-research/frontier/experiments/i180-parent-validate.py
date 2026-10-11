"""Detached I180 authentication and exclusive read-only replay receipts."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT/"frontier/experiments/i180_survivor_helper_connectivity"
REPORT = ROOT/"frontier/iterations/i180-survivor-helper-connectivity.md"
ANCHORS = {
    REPORT: "ee97afc179f45d40644f935d05956db17a785560fc249f5d47159b0ad2b42322",
    BASE/"seal.json": "0edee6b86197f691803982fb695396b5102cbf100a307dab6cd10c7900c8abda",
    BASE/"verify180.py": "4b5dbdbe7b518529b145c6ee2bb6a5562c235a56634c513365485a5dc098070e",
}
CONTEXT = {"README.md","frontier/README.md","frontier/TEN-FINDINGS.md","frontier/iterations/README.md"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_bytes())


def save(name, value):
    with (BASE.parent/("i180-parent-"+name+".json")).open("x") as out:
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
    assert seal["verifier_sha256"] == ANCHORS[BASE/"verify180.py"]
    controls = {BASE/n for n in ("inventory.json","prevalidation.json","seal.json")}
    assert {ROOT/n for n in inv["controls"]} == controls
    actual = {REPORT}
    for d in (BASE,ROOT/"frontier/sources/i180_survivor_helper_connectivity"):
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
    assert read(BASE/"inputs.json")["strict"] == inv["external"]
    assert "frontier/experiments/i179-parent-integration.json" in {z["path"] for z in inv["external"]}
    contexts = [dict(path=z["path"],actual=sha(ROOT/z["path"]),inventory=z["sha256"],
                     inherited=z["inherited"]) for z in inv["context"]]
    assert len(inv["replays"]) == len(pre["comparisons"]) == 2
    for replay,comparison in zip(inv["replays"],pre["comparisons"]):
        assert replay["function"] == comparison["function"] and comparison["byte_identical"]
        assert sha(ROOT/replay["payload"]) == comparison["sha256"]
    assert len(pre["probes"]) == 8 and all(p["blocked"] for p in pre["probes"])
    assert len(inv["owned"]) == 44 and len(inv["external"]) == 913
    return dict(status="PASS",owned=44,non_context_external=913,external_context_total=917,
                contexts=contexts,anchors={str(p.relative_to(ROOT)):h for p,h in ANCHORS.items()})


def main():
    before = authenticate()
    save("precheck",before)
    stdout,stderr = (BASE.parent/("i180-parent-replay-"+n) for n in ("stdout.json","stderr.txt"))
    with stdout.open("xb") as out,stderr.open("xb") as err:
        run = subprocess.run([sys.executable,"-I","-B",str(BASE/"verify180.py")],
                             cwd=ROOT,stdout=out,stderr=err,timeout=1200)
    assert run.returncode == 0 and not stderr.read_bytes()
    result = read(stdout)
    assert result["status"] == "PASS" and not result["prevalidation"]
    assert result["seal_sha256"] == ANCHORS[BASE/"seal.json"]
    assert len(result["comparisons"]) == 2 and all(z["byte_identical"] for z in result["comparisons"])
    assert len(result["probes"]) == 8 and all(z["blocked"] for z in result["probes"])
    assert before == authenticate()
    save("verification",dict(status="PASS",replay=result,postcheck=before,stderr="empty",
         context_policy="Historical drift allowed; current bytes fixed during execution.",
         clean_clone_reconstruction="not tested"))
    print("Parent replay PASS",result["runtime_seconds"],"seconds; 44 owned, 913 strict external, four contexts")


if __name__ == "__main__":
    main()
