"""Detached I181 authentication and exclusive read-only replay receipts."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT/"frontier/experiments/i181_six_cycle_helper"
SOURCE = ROOT/"frontier/sources/i181_six_cycle_helper"
REPORT = ROOT/"frontier/iterations/i181-six-cycle-helper.md"
ANCHORS = {
    REPORT: "446f5bbb28e249744903ad32d04e9b264979ff2e9a77ef2f107bce93e36d4e46",
    BASE/"seal.json": "22c454fbfd8806aaaa061ddf997e298fec1c27b5e4d9f4d8b6af2202219374e3",
    BASE/"verify181.py": "dd9a02176ef4f6c94e1f732f3c89dd39a59277cbaac72caffe5b6910c897f47b",
}
PAYLOADS = {
    "mandatory": "29c2240943d5f45b2ad44558e6c2fea9012d31e2823a157844c121d908f6aa94",
    "topology": "4c0ab64811a25094a5f001466695a036128742bb07a39e2e70afcd148b38320f",
}
CONTEXT = {"README.md","frontier/README.md","frontier/TEN-FINDINGS.md","frontier/iterations/README.md"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_bytes())


def save(name, value):
    with (BASE.parent/("i181-parent-"+name+".json")).open("x") as out:
        json.dump(value,out,indent=2,sort_keys=True)
        out.write("\n")


def authenticate():
    for p,h in ANCHORS.items():
        assert sha(p) == h,p
    inv,seal,pre = (read(BASE/n) for n in ("inventory.json","seal.json","prevalidation.json"))
    assert pre["status"] == "PASS"
    for name in ("inventory","prevalidation"):
        assert sha(BASE/(name+".json")) == seal[name+"_sha256"]
    for field in ("inventory_sha256","report_sha256","verifier_sha256"):
        assert pre[field] == seal[field] if field in pre else True
    assert seal["report_sha256"] == ANCHORS[REPORT]
    assert seal["verifier_sha256"] == ANCHORS[BASE/"verify181.py"]
    assert seal["mandatory_payload_sha256"] == PAYLOADS["mandatory"]
    assert seal["topology_payload_sha256"] == PAYLOADS["topology"]
    controls = {BASE/n for n in ("inventory.json","prevalidation.json","seal.json")}
    actual = {REPORT}
    for d in (BASE,SOURCE):
        actual |= {p for p in d.rglob("*") if p.is_file()}
    owned = {ROOT/z["path"] for z in inv["files"]}
    assert actual-controls == owned, (sorted(str(p) for p in actual-controls-owned),
                                      sorted(str(p) for p in owned-(actual-controls)))
    assert len(inv["files"]) == len({z["path"] for z in inv["files"]}) == seal["inventory_file_count"] == 29
    assert not any((ROOT/z["path"]).is_symlink() for z in inv["files"])
    for z in inv["files"]:
        p = ROOT/z["path"]
        assert p.resolve().is_relative_to(ROOT)
        assert sha(p) == z["sha256"] and p.stat().st_size == z["size"],p
    assert set(r.rstrip("/") for r in inv["exclusive_roots"]) == {str(REPORT.relative_to(ROOT)),
        "frontier/experiments/i181_six_cycle_helper","frontier/sources/i181_six_cycle_helper"}
    frozen = read(BASE/"inputs.json")
    strict = {z["path"] for z in frozen["strict"]}
    assert len(frozen["strict"]) == 972 and len(frozen["context"]) == 4
    assert {z["path"] for z in frozen["context"]} == CONTEXT
    assert not CONTEXT & strict
    for z in frozen["strict"]:
        p = ROOT/z["path"]
        assert p.resolve().is_relative_to(ROOT) and not p.is_symlink()
        assert sha(p) == z["sha256"] and p.stat().st_size == z["size"],p
    for z in frozen["context"]:
        p = ROOT/z["path"]
        assert p.resolve().is_relative_to(ROOT) and not p.is_symlink() and p.is_file()
    assert frozen["anchors"] == {str(p.relative_to(ROOT)):h for p,h in
        {ROOT/k:v for k,v in frozen["anchors"].items()}.items()}
    assert "frontier/experiments/i180-parent-integration.json" in strict
    chains = frozen["ancestor_chains"]
    assert [(c["iteration"],c["owned"],c["control_chain"]) for c in chains] == [
        (175,94,True),(176,59,True),(177,78,True),(178,81,True),(179,122,True),(180,44,True)]
    assert len(frozen["parent_evidence"]) == 15 and len(frozen["parent_membership"]) == 47
    contexts = [dict(path=z["path"],actual=sha(ROOT/z["path"]),frozen=z["sha256"])
                for z in frozen["context"]]
    # Replay determinism cross-check: prevalidation double replays match the seal payloads
    # after removal of the volatile runtime field.
    for key,retained in (("mandatory","mandatory-attempt-05.json"),("topology","topology-attempt-01.json")):
        canon = pre["diagnostics"][key]["sha256"]
        payload = read(BASE/retained)
        payload.pop("runtime_seconds",None)
        raw = json.dumps(payload,sort_keys=True,separators=(",",":")).encode()
        assert hashlib.sha256(raw).hexdigest() == canon,key
    return dict(status="PASS",owned=29,strict=972,contexts=contexts,
                anchors={str(p.relative_to(ROOT)):h for p,h in ANCHORS.items()},
                ancestor_chains=chains,parent_evidence=15,parent_membership=47)


def main():
    before = authenticate()
    save("precheck",before)
    stdout,stderr = (BASE.parent/("i181-parent-replay-"+n) for n in ("stdout.json","stderr.txt"))
    with stdout.open("xb") as out,stderr.open("xb") as err:
        run = subprocess.run([sys.executable,"-I","-B",str(BASE/"verify181.py")],
                             cwd=ROOT,stdout=out,stderr=err,timeout=1200)
    assert run.returncode == 0 and not stderr.read_bytes()
    result = read(stdout)
    assert result["status"] == "PASS" and result["E181"] == "UNRESOLVED"
    assert result["seal_sha256"] == ANCHORS[BASE/"seal.json"]
    assert result["report_sha256"] == ANCHORS[REPORT]
    assert result["package_checks"] >= 29
    assert len(result["blocked_probes"]) == 8 and all(p["status"] == "BLOCKED" for p in result["blocked_probes"])
    assert result["integrity_state"] == "UNCHANGED"
    for key in ("mandatory","topology"):
        assert len(result[key+"_replay"]["runtime_seconds"]) == 2
    assert before == authenticate()
    save("verification",dict(status="PASS",replay=result,postcheck=before,stderr="empty",
         context_policy="Historical drift allowed; current bytes fixed during execution.",
         clean_clone_reconstruction="not tested"))
    print("Parent replay PASS; 29 owned, 972 strict, four contexts;",
          [round(t,4) for t in result["mandatory_replay"]["runtime_seconds"]])


if __name__ == "__main__":
    main()
