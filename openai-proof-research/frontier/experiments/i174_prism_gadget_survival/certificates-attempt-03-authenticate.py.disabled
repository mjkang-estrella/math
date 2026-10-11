"""I174 independent byte authentication; never loads ancestor executables."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
SOURCE = ROOT / "frontier/sources/i174_prism_gadget_survival"
OLD = "frontier/experiments/i173_brace_high_loss_octagons/"
REPORT = "frontier/iterations/i173-brace-high-loss-octagons.md"
ANCHORS = {
    REPORT: "e06169dc4b72c42da7a26797eb73f8368222dc9e7d87290c909af7c243c52fc2",
    OLD + "seal.json": "6b824bffc72019f3c75dee02c70c1f0173b557cffc4275177f35bcb76356e609",
    OLD + "verify.py": "0d3db09c92da4b5c59a164a97daf05039660c16702096b95a9c8bf43e7f4778a",
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def authenticate():
    memory = {}
    def read(name):
        data = (ROOT / name).read_bytes()
        memory[name] = data
        return data
    for name, expected in ANCHORS.items():
        assert digest(read(name)) == expected, name
    seal = json.loads(memory[OLD + "seal.json"])
    inv = json.loads(read(OLD + "inventory.json"))
    assert digest(memory[OLD + "inventory.json"]) == seal["inventory_sha256"]
    pre = json.loads(read(OLD + "prevalidation.json"))
    assert digest(memory[OLD + "prevalidation.json"]) == seal["prevalidation_sha256"]
    assert pre["status"] == "PASS" and pre["prevalidation"]
    assert pre["inventory_sha256"] == seal["inventory_sha256"]
    assert len(inv["owned"]) == 62 and len(inv["external"]) == 205
    assert len(inv["context"]) == 4
    actual = {REPORT}
    for directory in (OLD, "frontier/sources/i173_brace_high_loss_octagons"):
        actual.update(str(p.relative_to(ROOT)) for p in (ROOT / directory).rglob("*") if p.is_file())
    assert actual == {x["path"] for x in inv["owned"]} | set(inv["controls"])
    for entry in inv["owned"] + inv["external"]:
        data = read(entry["path"])
        assert digest(data) == entry["sha256"], entry["path"]
        if "size" in entry:
            assert len(data) == entry["size"]
    context = []
    for entry in inv["context"]:
        h = digest(read(entry["path"]))
        context.append(dict(path=entry["path"], inherited=entry["sha256"], current=h,
                            drift=h != entry["sha256"]))
    extras = [
        "frontier/iterations/iteration174-prism-gadget-survival-brief.md",
        "frontier/iterations/i173-brace-high-loss-octagons-parent-disposition.md",
    ] + ["frontier/experiments/i173-parent-" + suffix for suffix in [
        "precheck.json", "replay-stdout.json", "replay-stderr.txt",
        "verification.json", "certificates.json"]]
    for name in extras:
        read(name)
    receipt = json.loads(memory["frontier/experiments/i173-parent-verification.json"])
    assert receipt["status"] == "PASS" and receipt["replay"]["runtime_seconds"] == 268.718492
    assert not memory["frontier/experiments/i173-parent-replay-stderr.txt"]
    bindings = [{"path": k, "sha256": digest(v), "size": len(v)}
                for k, v in sorted(memory.items()) if k not in {e["path"] for e in inv["context"]}]
    return memory, dict(status="PASS", anchors=ANCHORS, owned=62, external=205,
                        context=context, external_context_total=209, bindings=bindings,
                        ancestor_code="opaque bytes; neither read as implementation nor executed")


if __name__ == "__main__":
    _, receipt = authenticate()
    SOURCE.mkdir(parents=True, exist_ok=True)
    with (SOURCE / "authentication.json").open("x") as f:
        json.dump(receipt, f, indent=2, sort_keys=True)
        f.write("\n")
    print(json.dumps({k:v for k,v in receipt.items() if k != "bindings"}, indent=2))
