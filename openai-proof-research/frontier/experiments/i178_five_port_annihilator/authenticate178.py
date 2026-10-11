"""Fresh byte-only authentication. Ancestor source is never compiled or imported."""
import hashlib
import json
from pathlib import Path

ROOT = Path("/home/mj-kang/Documents/Dev/math/openai-proof-research")
OWN = ROOT / "frontier/experiments/i178_five_port_annihilator"
PRE = "frontier/experiments/i177_adjacent_port_surgery/"
CONTEXT = {"README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"}
ANCHORS = {
    "frontier/iterations/i177-adjacent-port-surgery.md":
        "4c37997b83da3238793a9850742fb4daac188442cbeeaf4a864a3af2cc01d8a3",
    PRE + "seal.json":
        "1ffbf11ad4970094ac4cffb75519c4b5267b72430cb27f2009e79db98abcbd9f",
    PRE + "verify177.py":
        "15c8c3be562d4723e1c1a33befb646042ac17271a224c217025789b6d25f3c5c",
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def record(path):
    data = (ROOT / path).read_bytes()
    return {"path": path, "sha256": sha(data), "size": len(data)}


def main():
    for p, h in ANCHORS.items():
        assert record(p)["sha256"] == h, p
    inv = json.loads((ROOT / (PRE + "inventory.json")).read_bytes())
    pre = json.loads((ROOT / (PRE + "prevalidation.json")).read_bytes())
    seal = json.loads((ROOT / (PRE + "seal.json")).read_bytes())
    assert (len(inv["owned"]), len(inv["external"]), len(inv["context"])) == (78, 585, 4)
    assert {r["path"] for r in inv["context"]} == CONTEXT
    for r in inv["owned"] + inv["external"]:
        assert record(r["path"]) == r, r["path"]
    for key, name in [("inventory_sha256", "inventory.json"),
                      ("prevalidation_sha256", "prevalidation.json")]:
        assert seal[key] == record(PRE + name)["sha256"]
    assert pre["status"] == "PASS" and pre["prevalidation"]
    assert pre["inventory_sha256"] == seal["inventory_sha256"]
    assert pre["report_sha256"] == seal["report_sha256"] == ANCHORS[
        "frontier/iterations/i177-adjacent-port-surgery.md"]
    assert pre["verifier_sha256"] == seal["verifier_sha256"] == ANCHORS[PRE+"verify177.py"]
    assert len(pre["probes"]) == 8 and all(p["blocked"] for p in pre["probes"])
    assert pre["context_before"] == pre["context_after"]
    for replay, comparison in zip(inv["replays"], pre["comparisons"]):
        assert comparison["byte_identical"]
        assert comparison["sha256"] == record(replay["payload"])["sha256"]
    roots = [ROOT / PRE, ROOT / "frontier/sources/i177_adjacent_port_surgery"]
    actual = {str(p.relative_to(ROOT)) for d in roots for p in d.rglob("*") if p.is_file()}
    actual.add("frontier/iterations/i177-adjacent-port-surgery.md")
    assert actual == {r["path"] for r in inv["owned"]} | set(inv["controls"])
    paths = {r["path"] for r in inv["owned"] + inv["external"]} | set(inv["controls"])
    paths |= {"frontier/iterations/iteration178-five-port-annihilator-brief.md",
              "frontier/iterations/iteration177-adjacent-port-surgery-brief.md",
              "frontier/iterations/i177-adjacent-port-surgery-parent-disposition.md"}
    for directory, pattern in [("frontier/experiments", "i177-parent-*"),
                               ("frontier/iterations", "iteration178*"),
                               ("frontier/iterations", "iteration177*")]:
        paths.update(str(p.relative_to(ROOT)) for p in (ROOT/directory).glob(pattern)
                     if p.is_file())
    frozen = {
        "status": "PASS", "ancestor_owned": 78, "ancestor_strict_external": 585,
        "ancestor_contexts": 4, "ancestor_membership_complete": True,
        "ancestor_control_chain": True, "detached_anchors": ANCHORS,
        "strict": [record(p) for p in sorted(paths-CONTEXT)],
        "context": [{**record(p), "inherited": next(r["sha256"] for r in inv["context"]
                                                   if r["path"] == p)}
                    for p in sorted(CONTEXT)],
        "policy": "Complete frozen input inventory before diagnostics; ancestors opaque."
    }
    with (OWN / "inputs.json").open("x") as f:
        json.dump(frozen, f, indent=2, sort_keys=True)
        f.write("\n")
    print(json.dumps({k: v for k, v in frozen.items() if k not in {"strict", "context"}},
                     sort_keys=True))


if __name__ == "__main__":
    main()
