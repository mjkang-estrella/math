"""I183 byte authentication and one-time immutable input freeze.

Binds the complete I182 package (25 owned files), the 1,014 strict
ancestor bindings carried by the I182 freeze, the I182 sources receipt,
and all i182-parent evidence (disposition, briefs, validator, replay
stdout/stderr, precheck/verification receipts, certificates, dispatch
archive and the final integration receipt, which arrived before this
freeze, so no supplement is needed).  The four ledger contexts are
recorded with current bytes and are drift-exempt (never fatal).

Ancestor Python is opaque hashed evidence: never executed, imported,
compiled or copied as implementation.

Usage:
    python3 -I -B auth183.py check    # full audit, writes nothing
    python3 -I -B auth183.py freeze   # writes inputs.json exactly once
"""
import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
BASE = "frontier/experiments/i183_cptp_survival"
PKG = "frontier/experiments/i182_controlled_extension"
PKG_SOURCES = "frontier/sources/i182_controlled_extension"
PARENT_REPORT = "frontier/iterations/i182-controlled-extension.md"
CONTEXT = ["README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"]
ANCHORS = {
    PARENT_REPORT:
        "6035bffd8b69ba08bf6a148fdd314bd704824e6bdd1942469afb0d343596ebc6",
    PKG + "/seal.json":
        "6fcbd83ab618636826cb2c9d7f71d18d22a316fcc12772501dc6fbac7668667c",
    PKG + "/verify182.py":
        "314696445a3e77ad2a6bde12e0cc4826454b70bc7e0529dfd33d9e00c00f2889",
}
GENERATED = ["inventory.json", "prevalidation.json", "seal.json"]
INTEGRATION = "frontier/experiments/i182-parent-integration.json"
REPORT = "frontier/iterations/i183-cptp-survival.md"


def row(path):
    data = (ROOT / path).read_bytes()
    return {"path": path, "sha256": hashlib.sha256(data).hexdigest(),
            "size": len(data)}


def digest(path):
    return row(path)["sha256"]


def load(path):
    return json.loads((ROOT / path).read_bytes())


def check_rows(rows):
    for item in rows:
        now = row(item["path"])
        assert (now["sha256"], now["size"]) == (item["sha256"], item["size"]), \
            item["path"]


def package_membership(declared):
    actual = set()
    for base in (PKG, PKG_SOURCES):
        for found in (ROOT / base).rglob("*"):
            if found.is_file():
                actual.add(str(found.relative_to(ROOT)))
    if (ROOT / PARENT_REPORT).is_file():
        actual.add(PARENT_REPORT)
    assert actual == set(declared), \
        (sorted(actual - set(declared)), sorted(set(declared) - actual))
    return sorted(actual)


def authenticate_parent():
    for path, wanted in ANCHORS.items():
        assert digest(path) == wanted, path
    inventory = load(PKG + "/inventory.json")
    assert inventory["iteration"] == 182
    assert inventory["owned_files"] == 25 == len(inventory["files"])
    owned_paths = []
    for entry in inventory["files"]:
        path = PKG + "/" + entry["name"]
        record = entry["sha256"]
        now = row(path)
        assert now["size"] == entry["bytes"] == record["size"], path
        assert now["sha256"] == record["sha256"], path
        assert entry["name"] in record["path"], path
        owned_paths.append(path)
    declared = owned_paths + [PKG + "/" + name for name in GENERATED]
    declared += [PARENT_REPORT, PKG_SOURCES + "/literature.md"]
    members = package_membership(declared)
    seal = load(PKG + "/seal.json")
    pre = load(PKG + "/prevalidation.json")
    assert seal["status"] == pre["status"] == "PASS"
    assert seal["report_sha256"] == ANCHORS[PARENT_REPORT]
    assert seal["verifier_sha256"] == ANCHORS[PKG + "/verify182.py"]
    assert seal["inventory_sha256"] == inventory["owned_sha256"]
    assert pre["inventory_sha256"] == inventory["owned_sha256"]
    for key, name in (("mandatory", seal["mandatory_name"]),
                      ("extension", seal["extension_name"])):
        assert seal[key + "_payload_sha256"] == digest(PKG + "/" + name)
        assert pre[key + "_payload_sha256"] == seal[key + "_payload_sha256"]
        assert pre["checks"][key + "_replay_1"]["byte_identical"] is True
        assert pre["checks"][key + "_replay_2"]["byte_identical"] is True
    frozen = load(PKG + "/inputs.json")
    assert len(frozen["strict"]) == 1014 and len(frozen["context"]) == 4
    check_rows(frozen["strict"])
    assert any(item["path"] ==
               "frontier/experiments/i181-parent-integration.json"
               for item in frozen["strict"])
    base181 = "frontier/experiments/i181_six_cycle_helper"
    anchors181 = frozen["anchors"]
    for path, wanted in anchors181.items():
        assert digest(path) == wanted, path
    inv181 = load(base181 + "/inventory.json")
    assert inv181["package"] == "I181"
    assert inv181["file_count"] == 29 == len(inv181["files"])
    check_rows(inv181["files"])
    declared181 = [item["path"] for item in inv181["files"]] + \
        [base181 + "/" + name for name in GENERATED]
    actual181 = set()
    for root_dir in (base181, base181.replace("/experiments/", "/sources/")):
        for found in (ROOT / root_dir).rglob("*"):
            if found.is_file():
                actual181.add(str(found.relative_to(ROOT)))
    report181 = "frontier/iterations/i181-six-cycle-helper.md"
    if (ROOT / report181).is_file():
        actual181.add(report181)
    assert actual181 == set(declared181)
    seal181 = load(base181 + "/seal.json")
    pre181 = load(base181 + "/prevalidation.json")
    assert pre181["status"] == "PASS"
    assert seal181["report_sha256"] == anchors181[report181]
    assert seal181["verifier_sha256"] == anchors181[base181 + "/verify181.py"]
    assert seal181["inventory_sha256"] == digest(base181 + "/inventory.json")
    assert seal181["prevalidation_sha256"] == \
        digest(base181 + "/prevalidation.json")
    assert seal181["inventory_file_count"] == 29
    chains = []
    names = sorted({item["path"] for item in frozen["strict"]
                    if item["path"].endswith("/inventory.json")
                    and "/i1" in item["path"]})
    for name in names:
        old = load(name)
        iteration = old.get("iteration")
        if not isinstance(iteration, int) or iteration < 175:
            continue
        base = str(Path(name).parent)
        check_rows(old["owned"])
        old_declared = {item["path"] for item in old["owned"]} | \
            set(old["controls"])
        old_actual = set()
        for root_dir in (base, base.replace("/experiments/", "/sources/")):
            for found in (ROOT / root_dir).rglob("*"):
                if found.is_file():
                    old_actual.add(str(found.relative_to(ROOT)))
        for item in old["owned"]:
            if item["path"].startswith("frontier/iterations/") and \
                    (ROOT / item["path"]).is_file():
                old_actual.add(item["path"])
        assert old_actual == old_declared, name
        old_seal = load(base + "/seal.json")
        old_pre = load(base + "/prevalidation.json")
        assert old_pre["status"] == "PASS"
        assert old_seal["inventory_sha256"] == digest(name)
        assert old_seal["prevalidation_sha256"] == \
            digest(base + "/prevalidation.json")
        assert old_pre["inventory_sha256"] == old_seal["inventory_sha256"]
        report = next(item["path"] for item in old["owned"]
                      if item["path"].startswith("frontier/iterations/"))
        assert old_seal["report_sha256"] == digest(report)
        assert old_seal["verifier_sha256"] == digest(
            base + "/verify" + str(iteration) + ".py")
        chains.append({"iteration": iteration, "owned": len(old["owned"]),
                       "membership": len(old_declared),
                       "control_chain": True})
    chains.append({"iteration": 181, "owned": 29,
                   "membership": len(declared181), "control_chain": True})
    chains.append({"iteration": 182, "owned": 25,
                   "membership": len(members), "control_chain": True})
    assert [c["iteration"] for c in chains] == \
        [175, 176, 177, 178, 179, 180, 181, 182]
    assert [c["owned"] for c in chains] == [94, 59, 78, 81, 122, 44, 29, 25]
    return frozen, members, chains


def parent_evidence():
    paths = set()
    for pattern in ("frontier/experiments/i182-parent-*",
                    "frontier/iterations/*182*",
                    "frontier/iterations/iteration183-*",
                    PKG_SOURCES + "/*"):
        for found in ROOT.glob(pattern):
            if found.is_file():
                paths.add(str(found.relative_to(ROOT)))
    paths.discard(REPORT)
    return sorted(paths)


def build_freeze():
    frozen, members, chains = authenticate_parent()
    evidence = parent_evidence()
    assert INTEGRATION in evidence, \
        "I182 final integration receipt must be bound in the original freeze"
    assert digest(PARENT_REPORT) == ANCHORS[PARENT_REPORT]
    strict = {item["path"] for item in frozen["strict"]}
    strict |= {PKG + "/" + entry["name"]
               for entry in load(PKG + "/inventory.json")["files"]}
    strict |= set(evidence)
    assert not strict.intersection(CONTEXT)
    obj = {
        "iteration": 183,
        "status": "PASS",
        "strict": [row(path) for path in sorted(strict)],
        "context": [row(path) for path in CONTEXT],
        "anchors": ANCHORS,
        "parent_membership": members,
        "parent_evidence": evidence,
        "ancestor_chains": chains,
        "policy": "Exclusive complete freeze before any mathematical "
                  "diagnostics; never overwrite.",
        "receipt": "I182 final integration receipt present in the "
                   "original freeze; no supplement needed.",
        "ancestor_python": "Opaque bytes, not read as implementation, "
                           "compiled, imported or executed.",
    }
    return obj, len(strict)


def freeze():
    obj, count = build_freeze()
    target = ROOT / BASE / "inputs.json"
    with target.open("x") as stream:
        json.dump(obj, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"status": "PASS", "strict": count, "contexts": 4,
                      "chains": [c["iteration"] for c in
                                 obj["ancestor_chains"]],
                      "parent_evidence": len(obj["parent_evidence"])}))


def frozen_check():
    obj = load(BASE + "/inputs.json")
    check_rows(obj["strict"])
    check_rows(obj["context"])
    fresh, members, chains = authenticate_parent()
    assert chains == obj["ancestor_chains"]
    assert members == obj["parent_membership"]
    assert parent_evidence() == obj["parent_evidence"], \
        "New parent evidence would need an additive frozen supplement"
    return obj


if __name__ == "__main__":
    if len(sys.argv) == 2 and sys.argv[1] == "check":
        _, count = build_freeze()
        print(json.dumps({"status": "CHECK-ONLY PASS", "strict": count}))
    else:
        freeze()
