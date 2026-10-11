"""I181 byte authentication only. Ancestor programs remain opaque."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[3]
BASE = "frontier/experiments/i181_six_cycle_helper"
SOURCE = "frontier/sources/i181_six_cycle_helper"
REPORT = "frontier/iterations/i181-six-cycle-helper.md"
CONTEXT = ["README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"]
PARENT = "frontier/experiments/i180_survivor_helper_connectivity"
ANCHORS = {
    "frontier/iterations/i180-survivor-helper-connectivity.md":
        "ee97afc179f45d40644f935d05956db17a785560fc249f5d47159b0ad2b42322",
    PARENT + "/seal.json":
        "0edee6b86197f691803982fb695396b5102cbf100a307dab6cd10c7900c8abda",
    PARENT + "/verify180.py":
        "4b5dbdbe7b518529b145c6ee2bb6a5562c235a56634c513365485a5dc098070e",
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def load(name):
    return json.loads((ROOT / name).read_bytes())


def record(name):
    data = (ROOT / name).read_bytes()
    return {"path": name, "sha256": digest(data), "size": len(data)}


def check(rows):
    for row in rows:
        assert record(row["path"]) == {k: row[k] for k in ("path", "sha256", "size")}, row["path"]


def membership(inv, parent):
    declared = {r["path"] for r in inv["owned"]} | set(inv["controls"])
    dirs = [parent, parent.replace("/experiments/", "/sources/")]
    actual = {str(p.relative_to(ROOT)) for d in dirs
              for p in (ROOT / d).rglob("*") if p.is_file()}
    reports = {p for p in declared if p.startswith("frontier/iterations/")}
    actual |= {p for p in reports if (ROOT / p).is_file()}
    assert actual == declared, (parent, sorted(actual - declared), sorted(declared - actual))
    return sorted(actual)


def authenticate_parent():
    for name, expected in ANCHORS.items():
        assert record(name)["sha256"] == expected, name
    inv = load(PARENT + "/inventory.json")
    assert (len(inv["owned"]), len(inv["external"]), len(inv["context"])) == (44, 913, 4)
    assert sorted(r["path"] for r in inv["context"]) == sorted(CONTEXT)
    check(inv["owned"] + inv["external"])
    membership(inv, PARENT)
    frozen = load(PARENT + "/inputs.json")
    assert frozen["strict"] == inv["external"]
    assert "frontier/experiments/i179-parent-integration.json" in {
        r["path"] for r in frozen["strict"]}
    chains = []
    names = [r["path"] for r in inv["external"] if r["path"].endswith("/inventory.json")
             and "/i17" in r["path"]] + [PARENT + "/inventory.json"]
    for name in names:
        old = load(name)
        if old.get("iteration", 0) < 175:
            continue
        parent = str(Path(name).parent)
        check(old["owned"])
        members = membership(old, parent)
        seal = load(parent + "/seal.json")
        pre = load(parent + "/prevalidation.json")
        assert pre["status"] == "PASS"
        assert seal["inventory_sha256"] == record(name)["sha256"]
        assert seal["prevalidation_sha256"] == record(parent + "/prevalidation.json")["sha256"]
        assert pre["inventory_sha256"] == seal["inventory_sha256"]
        for key, filename in [("report_sha256", next(
                r["path"] for r in old["owned"] if r["path"].startswith("frontier/iterations/"))),
                              ("verifier_sha256", parent + "/verify" + str(old["iteration"]) + ".py")]:
            assert seal[key] == record(filename)["sha256"]
        chains.append({"iteration": old["iteration"], "owned": len(old["owned"]),
                       "membership": len(members), "control_chain": True})
    return inv, chains


def extras():
    paths = {str(p.relative_to(ROOT))
             for pat in ("frontier/experiments/i180-parent-*",
                         "frontier/iterations/*180*",
                         "frontier/iterations/iteration181-*")
             for p in ROOT.glob(pat) if p.is_file()}
    paths.discard(REPORT)
    return sorted(paths)


def freeze():
    inv, chains = authenticate_parent()
    strict = {r["path"] for r in inv["owned"] + inv["external"]} | set(inv["controls"]) | set(extras())
    assert not strict.intersection(CONTEXT)
    obj = {"iteration": 181, "status": "PASS", "strict": [record(p) for p in sorted(strict)],
           "context": [record(p) for p in CONTEXT], "anchors": ANCHORS,
           "parent_membership": membership(inv, PARENT), "parent_evidence": extras(),
           "ancestor_chains": chains,
           "policy": "Exclusive complete freeze before any mathematical diagnostics; never overwrite.",
           "receipt": "I180 final integration receipt present in original freeze.",
           "ancestor_python": "Opaque bytes, not read as implementation, compiled, imported or executed."}
    with (ROOT / BASE / "inputs.json").open("x") as stream:
        json.dump(obj, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"status": "PASS", "strict": len(strict), "contexts": 4,
                      "chains": chains, "parent_evidence": len(extras())}))


def frozen_check():
    obj = load(BASE + "/inputs.json")
    check(obj["strict"] + obj["context"])
    inv, chains = authenticate_parent()
    assert chains == obj["ancestor_chains"]
    assert membership(inv, PARENT) == obj["parent_membership"]
    assert extras() == obj["parent_evidence"], "New parent evidence needs additive frozen supplement"
    return obj


if __name__ == "__main__":
    freeze()
