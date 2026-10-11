"""I182 byte authentication and input freeze. Ancestor programs are opaque."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
BASE = "frontier/experiments/i182_controlled_extension"
SOURCE = "frontier/sources/i182_controlled_extension"
REPORT = "frontier/iterations/i182-controlled-extension.md"
CONTEXT = ["README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"]
PARENT = "frontier/experiments/i181_six_cycle_helper"
PARENT_REPORT = "frontier/iterations/i181-six-cycle-helper.md"
ANCHORS = {
    PARENT_REPORT:
        "446f5bbb28e249744903ad32d04e9b264979ff2e9a77ef2f107bce93e36d4e46",
    PARENT + "/seal.json":
        "22c454fbfd8806aaaa061ddf997e298fec1c27b5e4d9f4d8b6af2202219374e3",
    PARENT + "/verify181.py":
        "dd9a02176ef4f6c94e1f732f3c89dd39a59277cbaac72caffe5b6910c897f47b",
}
GENERATED = ["inventory.json", "prevalidation.json", "seal.json"]
INTEGRATION = "frontier/experiments/i181-parent-integration.json"


def sha(path):
    data = (ROOT / path).read_bytes()
    return {"path": path, "sha256": hashlib.sha256(data).hexdigest(), "size": len(data)}


def load(path):
    return json.loads((ROOT / path).read_bytes())


def verify_rows(rows):
    for row in rows:
        now = sha(row["path"])
        assert (now["sha256"], now["size"]) == (row["sha256"], row["size"]), row["path"]


def dir_membership(paths, report):
    declared = set(paths)
    actual = set()
    for base in (PARENT, PARENT.replace("/experiments/", "/sources/")):
        for f in (ROOT / base).rglob("*"):
            if f.is_file():
                actual.add(str(f.relative_to(ROOT)))
    if (ROOT / report).is_file():
        actual.add(report)
    assert actual == declared, (sorted(actual - declared), sorted(declared - actual))
    return sorted(actual)


def authenticate_parent():
    for path, digest in ANCHORS.items():
        assert sha(path)["sha256"] == digest, path
    inv = load(PARENT + "/inventory.json")
    assert inv["package"] == "I181" and inv["file_count"] == 29 == len(inv["files"])
    verify_rows(inv["files"])
    declared = [r["path"] for r in inv["files"]] + [PARENT + "/" + g for g in GENERATED]
    members = dir_membership(declared, PARENT_REPORT)
    seal = load(PARENT + "/seal.json")
    pre = load(PARENT + "/prevalidation.json")
    assert pre["status"] == "PASS"
    assert seal["report_sha256"] == ANCHORS[PARENT_REPORT]
    assert seal["verifier_sha256"] == ANCHORS[PARENT + "/verify181.py"]
    assert seal["inventory_sha256"] == sha(PARENT + "/inventory.json")["sha256"]
    assert seal["prevalidation_sha256"] == sha(PARENT + "/prevalidation.json")["sha256"]
    assert seal["inventory_file_count"] == 29
    frozen = load(PARENT + "/inputs.json")
    assert (len(frozen["strict"]), len(frozen["context"])) == (972, 4)
    verify_rows(frozen["strict"])
    assert "frontier/experiments/i180-parent-integration.json" in {
        r["path"] for r in frozen["strict"]}
    chains = []
    names = sorted({r["path"] for r in frozen["strict"]
                    if r["path"].endswith("/inventory.json") and "/i1" in r["path"]})
    for name in names:
        old = load(name)
        iteration = old.get("iteration")
        if not isinstance(iteration, int) or iteration < 175:
            continue
        base = str(Path(name).parent)
        verify_rows(old["owned"])
        old_declared = {r["path"] for r in old["owned"]} | set(old["controls"])
        old_actual = set()
        for root_dir in (base, base.replace("/experiments/", "/sources/")):
            for f in (ROOT / root_dir).rglob("*"):
                if f.is_file():
                    old_actual.add(str(f.relative_to(ROOT)))
        for r in old["owned"]:
            if r["path"].startswith("frontier/iterations/") and (ROOT / r["path"]).is_file():
                old_actual.add(r["path"])
        assert old_actual == old_declared, name
        old_seal = load(base + "/seal.json")
        old_pre = load(base + "/prevalidation.json")
        assert old_pre["status"] == "PASS"
        assert old_seal["inventory_sha256"] == sha(name)["sha256"]
        assert old_seal["prevalidation_sha256"] == sha(base + "/prevalidation.json")["sha256"]
        assert old_pre["inventory_sha256"] == old_seal["inventory_sha256"]
        report = next(r["path"] for r in old["owned"]
                      if r["path"].startswith("frontier/iterations/"))
        assert old_seal["report_sha256"] == sha(report)["sha256"]
        assert old_seal["verifier_sha256"] == sha(
            base + "/verify" + str(iteration) + ".py")["sha256"]
        chains.append({"iteration": iteration, "owned": len(old["owned"]),
                       "membership": len(old_declared), "control_chain": True})
    chains.append({"iteration": 181, "owned": 29, "membership": len(members),
                   "control_chain": True})
    assert [c["iteration"] for c in chains] == [175, 176, 177, 178, 179, 180, 181]
    assert [c["owned"] for c in chains] == [94, 59, 78, 81, 122, 44, 29]
    return frozen, members, chains


def parent_evidence():
    paths = set()
    for pattern in ("frontier/experiments/i181-parent-*",
                    "frontier/iterations/*181*",
                    "frontier/iterations/iteration182-*"):
        for f in ROOT.glob(pattern):
            if f.is_file():
                paths.add(str(f.relative_to(ROOT)))
    paths.discard(REPORT)
    return sorted(paths)


def freeze():
    frozen, members, chains = authenticate_parent()
    evidence = parent_evidence()
    assert INTEGRATION in evidence, "I181 final integration receipt must be bound"
    strict = {r["path"] for r in frozen["strict"]}
    strict |= {r["path"] for r in load(PARENT + "/inventory.json")["files"]}
    strict |= set(evidence)
    assert not strict.intersection(CONTEXT)
    obj = {
        "iteration": 182,
        "status": "PASS",
        "strict": [sha(p) for p in sorted(strict)],
        "context": [sha(p) for p in CONTEXT],
        "anchors": ANCHORS,
        "parent_membership": members,
        "parent_evidence": evidence,
        "ancestor_chains": chains,
        "policy": "Exclusive complete freeze before any mathematical diagnostics; never overwrite.",
        "receipt": "I181 final integration receipt present in original freeze; no supplement needed.",
        "ancestor_python": "Opaque bytes, not read as implementation, compiled, imported or executed.",
    }
    with (ROOT / BASE / "inputs.json").open("x") as stream:
        json.dump(obj, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"status": "PASS", "strict": len(strict), "contexts": 4,
                      "chains": [c["iteration"] for c in chains],
                      "parent_evidence": len(evidence)}))


def frozen_check():
    obj = load(BASE + "/inputs.json")
    verify_rows(obj["strict"])
    verify_rows(obj["context"])
    frozen, members, chains = authenticate_parent()
    assert chains == obj["ancestor_chains"]
    assert members == obj["parent_membership"]
    assert parent_evidence() == obj["parent_evidence"], \
        "New parent evidence needs additive frozen supplement"
    return obj


if __name__ == "__main__":
    freeze()
