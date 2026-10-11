"""Fresh byte authentication only. No ancestor source is executed or imported."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
HERE = ROOT / "frontier/experiments/i179_path_recombination"
OLD = "frontier/experiments/i178_five_port_annihilator/"
CONTEXTS = ("README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
            "frontier/iterations/README.md")
ANCHORS = {
    "frontier/iterations/i178-five-port-annihilator.md":
    "77bbc27865e326b5b5e2eebd52f61437683b260feb82c6ed811b14216c2bdc78",
    OLD + "seal.json":
    "6ae31f2775f1c2af44f47f7637905a104e9981182d4cf5dd656021317988f5f0",
    OLD + "verify178.py":
    "b000b7c6bfe6c926c2820731bf093d808f177fadfb5909009a131d95be61f531",
}


def digest(b):
    return hashlib.sha256(b).hexdigest()


def record(p):
    b = (ROOT / p).read_bytes()
    return dict(path=p, sha256=digest(b), size=len(b))


def authenticate():
    inv = json.loads((ROOT / (OLD + "inventory.json")).read_bytes())
    pre = json.loads((ROOT / (OLD + "prevalidation.json")).read_bytes())
    seal = json.loads((ROOT / (OLD + "seal.json")).read_bytes())
    inputs = json.loads((ROOT / (OLD + "inputs.json")).read_bytes())
    assert (len(inv["owned"]), len(inv["external"]), len(inv["context"])) == (81, 678, 4)
    assert {x["path"] for x in inv["context"]} == set(CONTEXTS)
    for p, h in ANCHORS.items():
        assert record(p)["sha256"] == h, p
    for row in inv["owned"] + inv["external"]:
        assert record(row["path"]) == row, row["path"]
    assert inputs["strict"] == inv["external"]
    ih = record(OLD + "inventory.json")["sha256"]
    assert pre["status"] == "PASS" and pre["prevalidation"] is True
    assert pre["inventory_sha256"] == ih == seal["inventory_sha256"]
    assert seal["prevalidation_sha256"] == record(OLD + "prevalidation.json")["sha256"]
    assert seal["report_sha256"] == ANCHORS["frontier/iterations/i178-five-port-annihilator.md"]
    assert seal["verifier_sha256"] == ANCHORS[OLD + "verify178.py"]
    assert len(pre["probes"]) == 8 and all(x["blocked"] for x in pre["probes"])
    assert len(pre["comparisons"]) == 2 and all(x["byte_identical"] for x in pre["comparisons"])
    actual = {"frontier/iterations/i178-five-port-annihilator.md"}
    for folder in (OLD, "frontier/sources/i178_five_port_annihilator/"):
        actual.update(str(p.relative_to(ROOT)) for p in (ROOT / folder).rglob("*") if p.is_file())
    assert actual == {x["path"] for x in inv["owned"]} | set(inv["controls"])
    paths = actual | {x["path"] for x in inv["external"]}
    paths.add("frontier/iterations/i178-five-port-annihilator-parent-disposition.md")
    paths.add("frontier/iterations/iteration179-path-recombination-brief.md")
    paths.update(str(p.relative_to(ROOT)) for p in
                 (ROOT / "frontier/experiments").glob("i178-parent-*") if p.is_file())
    paths.update(str(p.relative_to(ROOT)) for p in
                 (ROOT / "frontier/iterations").glob("iteration179-*-task.json") if p.is_file())
    assert not paths.intersection(CONTEXTS)
    return dict(status="PASS", ancestor_owned=81, ancestor_strict_external=678,
                ancestor_contexts=4, ancestor_membership_complete=True,
                ancestor_control_chain=True, predignostic_ancestor_inputs_equal=True,
                detached_anchors=ANCHORS, strict=[record(p) for p in sorted(paths)],
                context=[dict(record(p), inherited=next(x["sha256"] for x in inv["context"]
                                                       if x["path"] == p)) for p in CONTEXTS],
                policy="Frozen before mathematical diagnostics; ancestor Python opaque bytes.",
                missing_at_freeze=[p for p in [
                    "frontier/experiments/i178-parent-integration.json"]
                    if not (ROOT / p).exists()])


if __name__ == "__main__":
    data = authenticate()
    HERE.mkdir(parents=True, exist_ok=True)
    with (HERE / "inputs.json").open("x") as f:
        json.dump(data, f, indent=2, sort_keys=True)
        f.write("\n")
    print(json.dumps({k: v for k, v in data.items() if k not in ("strict", "context")}, indent=2))
    print("strict inputs:", len(data["strict"]))
