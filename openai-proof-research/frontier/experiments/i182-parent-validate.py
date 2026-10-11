"""Detached I182 authentication and exclusive read-only replay receipts."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT/"frontier/experiments/i182_controlled_extension"
SOURCE = ROOT/"frontier/sources/i182_controlled_extension"
REPORT = ROOT/"frontier/iterations/i182-controlled-extension.md"
ANCHORS = {
    REPORT: "6035bffd8b69ba08bf6a148fdd314bd704824e6bdd1942469afb0d343596ebc6",
    BASE/"seal.json": "6fcbd83ab618636826cb2c9d7f71d18d22a316fcc12772501dc6fbac7668667c",
    BASE/"verify182.py": "314696445a3e77ad2a6bde12e0cc4826454b70bc7e0529dfd33d9e00c00f2889",
}
PAYLOADS = {
    "mandatory": "c3806b7572ef3a6ddc6729436c9bfe6edd55c7d877d60351cc46fce1644f7cd6",
    "extension": "8f5bc21ed73f55582b1dcf7014f246c95558e7c70aad5d9fc16c67f6dc2812fa",
}
CONTEXT = {"README.md","frontier/README.md","frontier/TEN-FINDINGS.md","frontier/iterations/README.md"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_bytes())


def save(name, value):
    with (BASE.parent/("i182-parent-"+name+".json")).open("x") as out:
        json.dump(value,out,indent=2,sort_keys=True)
        out.write("\n")


def authenticate():
    for p,h in ANCHORS.items():
        assert sha(p) == h,p
    inv,seal,pre = (read(BASE/n) for n in ("inventory.json","seal.json","prevalidation.json"))
    assert pre["status"] == "PASS"
    assert inv["iteration"] == 182 and seal["iteration"] == 182
    assert inv["owned_sha256"] == seal["inventory_sha256"] == pre["inventory_sha256"]
    assert seal["report_sha256"] == ANCHORS[REPORT]
    assert seal["verifier_sha256"] == ANCHORS[BASE/"verify182.py"]
    assert seal["mandatory_payload_sha256"] == PAYLOADS["mandatory"]
    assert seal["extension_payload_sha256"] == PAYLOADS["extension"]
    assert sha(BASE/seal["mandatory_name"]) == PAYLOADS["mandatory"]
    assert sha(BASE/seal["extension_name"]) == PAYLOADS["extension"]
    # Owned membership: package directory plus source receipt and report.
    owned_names = set(inv["owned_sha256"])
    assert len(owned_names) == len(inv["files"]) == inv["owned_files"] == 25
    actual = {p.name for p in BASE.iterdir() if p.is_file()} - {"inventory.json","prevalidation.json","seal.json"}
    assert actual == owned_names, (sorted(actual-owned_names),sorted(owned_names-actual))
    def digest_of(value):
        return value["sha256"] if isinstance(value,dict) else value
    for row in inv["files"]:
        p = BASE/row["name"]
        digest = digest_of(row["sha256"])
        assert digest_of(inv["owned_sha256"][row["name"]]) == digest,row["name"]
        assert not p.is_symlink() and sha(p) == digest and p.stat().st_size == row["bytes"],row["name"]
    assert (SOURCE/"literature.md").is_file() and REPORT.is_file()
    # Frozen inputs: strict bindings byte-checked; contexts recorded, drift-exempt.
    frozen = read(BASE/"inputs.json")
    assert frozen["iteration"] == 182 and frozen["status"] == "PASS"
    assert len(frozen["strict"]) == 1014 and len(frozen["context"]) == 4
    assert {z["path"] for z in frozen["context"]} == CONTEXT
    assert not CONTEXT & {z["path"] for z in frozen["strict"]}
    for z in frozen["strict"]:
        p = ROOT/z["path"]
        assert p.resolve().is_relative_to(ROOT) and not p.is_symlink()
        assert sha(p) == z["sha256"] and p.stat().st_size == z["size"],z["path"]
    for z in frozen["context"]:
        p = ROOT/z["path"]
        assert p.resolve().is_relative_to(ROOT) and not p.is_symlink() and p.is_file()
    assert frozen["anchors"] == {
        "frontier/iterations/i181-six-cycle-helper.md":
            "446f5bbb28e249744903ad32d04e9b264979ff2e9a77ef2f107bce93e36d4e46",
        "frontier/experiments/i181_six_cycle_helper/seal.json":
            "22c454fbfd8806aaaa061ddf997e298fec1c27b5e4d9f4d8b6af2202219374e3",
        "frontier/experiments/i181_six_cycle_helper/verify181.py":
            "dd9a02176ef4f6c94e1f732f3c89dd39a59277cbaac72caffe5b6910c897f47b"}
    for path,h in frozen["anchors"].items():
        assert sha(ROOT/path) == h,path
    chains = frozen["ancestor_chains"]
    assert [(c["iteration"],c["owned"],c["control_chain"]) for c in chains] == [
        (175,94,True),(176,59,True),(177,78,True),(178,81,True),(179,122,True),
        (180,44,True),(181,29,True)]
    assert len(frozen["parent_evidence"]) == 16
    assert "frontier/experiments/i181-parent-integration.json" in frozen["parent_evidence"]
    assert len(frozen["parent_membership"]) == 32
    contexts = [dict(path=z["path"],frozen=z["sha256"],current=sha(ROOT/z["path"]),
                     drifted=sha(ROOT/z["path"]) != z["sha256"]) for z in frozen["context"]]
    # Prevalidation double replays match the seal payloads minus volatile runtime.
    for key,retained in (("mandatory",seal["mandatory_name"]),("extension",seal["extension_name"])):
        payload = read(BASE/retained)
        payload.pop("runtime_seconds",None)
        raw = json.dumps(payload,sort_keys=True,separators=(",",":")).encode()
        digest = hashlib.sha256(raw).hexdigest()
        assert pre["checks"][key+"_replay_1"]["sha256"] == digest == pre["checks"][key+"_replay_2"]["sha256"],key
    return dict(status="PASS",owned=25,strict=1014,contexts=contexts,
                anchors={str(p.relative_to(ROOT)):h for p,h in ANCHORS.items()},
                ancestor_chains=[c["iteration"] for c in chains],parent_evidence=16)


def main():
    before = authenticate()
    save("precheck",before)
    stdout,stderr = (BASE.parent/("i182-parent-replay-"+n) for n in ("stdout.json","stderr.txt"))
    with stdout.open("xb") as out,stderr.open("xb") as err:
        run = subprocess.run([sys.executable,"-I","-B",str(BASE/"verify182.py")],
                             cwd=ROOT,stdout=out,stderr=err,timeout=1200)
    assert run.returncode == 0 and not stderr.read_bytes()
    result = read(stdout)
    assert result["status"] == "PASS" and result["owned_files"] == 25
    assert result["report_sha256"] == ANCHORS[REPORT]
    assert len(result["blocked_probes"]) == 8 and all(p["status"] == "BLOCKED" for p in result["blocked_probes"])
    assert before == authenticate()
    save("verification",dict(status="PASS",replay=result,postcheck=before,stderr="empty",
         context_policy="Four ledger contexts drift-exempt and recorded; strict bindings byte-fixed during execution.",
         verifier_scope="sealed verifier checks package/payloads/replays/probes; strict binding bytes checked by this parent harness",
         clean_clone_reconstruction="not tested"))
    print("Parent replay PASS; 25 owned, 1014 strict, four contexts; mandatory",
          round(result["mandatory_replay_seconds"],4),"s; extension",
          round(result["extension_replay_seconds"],4),"s")


if __name__ == "__main__":
    main()
