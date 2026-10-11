"""Fresh byte authentication; no ancestor executable is loaded."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
EXP = ROOT / "frontier/experiments/i175_affected_prism_exterior"
SRC = ROOT / "frontier/sources/i175_affected_prism_exterior"
OLD = "frontier/experiments/i174_prism_gadget_survival/"
CONTEXT = ["README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"]


def sha(b):
    return hashlib.sha256(b).hexdigest()


def dump(x):
    return (json.dumps(x, sort_keys=True, indent=2) + "\n").encode()


def authenticate():
    anchors = {
        "frontier/iterations/i174-prism-gadget-survival.md":
        "5690d67776a455018d1906ba778ce6b4e3afd8258cbbaeb8b2e1f7e66bff8cca",
        OLD + "seal.json":
        "b63e358e0506567a2098d61dfe164a2f2b4db721488105d16dd238cdc06886ef",
        OLD + "verify.py":
        "2a9df59029ea699daab69d4355e8934faf2791c230a6775102fb2e8e00aa4e83",
    }
    memory = {}

    def read(path, expected=None, size=None):
        b = (ROOT / path).read_bytes()
        assert expected is None or sha(b) == expected, path
        assert size is None or len(b) == size, path
        memory[path] = b
        return b

    for p, h in anchors.items():
        read(p, h)
    seal = json.loads(memory[OLD + "seal.json"])
    inv = json.loads(read(OLD + "inventory.json", seal["inventory_sha256"]))
    pre = json.loads(read(OLD + "prevalidation.json", seal["prevalidation_sha256"]))
    assert pre["status"] == "PASS"
    assert (len(inv["owned"]), len(inv["external"]), len(inv["context"])) == (107, 277, 4)
    assert sorted(x["path"] for x in inv["context"]) == sorted(CONTEXT)
    for x in inv["owned"] + inv["external"]:
        read(x["path"], x["sha256"], x["size"])
    owned = {x["path"] for x in inv["owned"]}
    actual = {"frontier/iterations/i174-prism-gadget-survival.md"}
    for directory in [ROOT / OLD, ROOT / "frontier/sources/i174_prism_gadget_survival"]:
        actual.update(str(p.relative_to(ROOT)) for p in directory.rglob("*") if p.is_file())
    assert actual == owned | set(inv["controls"])
    transition = json.loads(memory["frontier/sources/i174_prism_gadget_survival/parent-disposition-transition.json"])
    before = memory[transition["old_snapshot"]]
    after = memory[transition["new_snapshot"]]
    note = memory[transition["inserted_note"]]
    assert (len(before), len(after), len(note)) == (6035, 6539, 504)
    assert after.count(note) == 1 and after.replace(note, b"", 1) == before
    assert memory[OLD + "build-failure-01-stdout.txt"] == b""
    assert b"AssertionError" in memory[OLD + "build-failure-01-stderr.txt"]
    extras = [
        "AGENTS.md", "sources/upstream.json", "sources/CONTENTS.md", "sources/preprints-tree.json",
        "frontier/iterations/iteration175-affected-prism-exterior-brief.md",
        "frontier/iterations/i174-prism-gadget-survival-parent-disposition.md",
    ]
    extras += [str(p.relative_to(ROOT)) for p in
               (ROOT / "frontier/experiments").glob("i174-parent-*") if p.is_file()]
    for p in extras:
        read(p)
    receipt = json.loads(memory["frontier/experiments/i174-parent-verification.json"])
    assert receipt["status"] == "PASS" and receipt["stderr"] == "empty"
    assert receipt["replay"]["runtime_seconds"] == 17.08744652697351
    assert len(receipt["replay"]["probes"]) == 8
    assert all(x["blocked"] for x in receipt["replay"]["probes"])
    assert all(x["byte_identical"] for x in receipt["replay"]["comparisons"])
    contexts = [dict(x, actual=sha(read(x["path"]))) for x in inv["context"]]
    bindings = [{"path": p, "sha256": sha(b), "size": len(b)}
                for p, b in sorted(memory.items()) if p not in CONTEXT]
    return memory, {"status": "PASS", "anchors": anchors, "bindings": bindings,
                    "context": contexts, "I174_owned": 107, "I174_external": 277,
                    "I174_context": 4, "I174_external_context_total": 281,
                    "transition": "exact 6035/6539 versions and 504-byte insertion authenticated",
                    "ancestor_execution": False, "parent_receipt_seconds": 17.08744652697351}


if __name__ == "__main__":
    _, receipt = authenticate()
    SRC.mkdir(parents=True, exist_ok=True)
    with (SRC / "authentication.json").open("xb") as f:
        f.write(dump(receipt))
    print(json.dumps({k: v for k, v in receipt.items() if k not in ("bindings", "context")}))
