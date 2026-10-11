"""Fresh byte-only authentication. No ancestor source is executed."""
import hashlib
import json
from pathlib import Path

ROOT = Path("/home/mj-kang/Documents/Dev/math/openai-proof-research")
BASE = ROOT / "frontier/experiments/i177_adjacent_port_surgery"
OLD = "frontier/experiments/i176_uniform_five_port_rank/"
CONTEXTS = ("README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
            "frontier/iterations/README.md")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def authenticate():
    invbytes = (ROOT / (OLD + "inventory.json")).read_bytes()
    inv = json.loads(invbytes)
    sealbytes = (ROOT / (OLD + "seal.json")).read_bytes()
    seal = json.loads(sealbytes)
    expected = {
        "frontier/iterations/i176-uniform-five-port-rank.md":
        "e5cf0be3222c1b60152659e968a1ce571832b243c40e3adceb3514b2d7324721",
        OLD + "seal.json":
        "72560bdafd354f0e0e5cb405a032fa6eb72f2b4e6f92c6a1ec6c3736d3fdc22b",
        OLD + "verify176.py":
        "ff1f84ec5853c22c7e37f5049ff80deda9a02578563cb7b14ed82c338cf22ec0",
    }
    for path, sha in expected.items():
        assert digest((ROOT / path).read_bytes()) == sha, path
    assert len(inv["owned"]) == 59 and len(inv["external"]) == 507
    assert {x["path"] for x in inv["context"]} == set(CONTEXTS)
    bindings = {}
    for entry in inv["owned"] + inv["external"]:
        data = (ROOT / entry["path"]).read_bytes()
        assert (len(data), digest(data)) == (entry["size"], entry["sha256"]), entry
        assert entry["path"] not in bindings
        bindings[entry["path"]] = entry
    controls = set(inv["controls"])
    actual = {"frontier/iterations/i176-uniform-five-port-rank.md"}
    for dirname in ("frontier/experiments/i176_uniform_five_port_rank",
                    "frontier/sources/i176_uniform_five_port_rank"):
        actual.update(str(p.relative_to(ROOT)) for p in (ROOT / dirname).rglob("*") if p.is_file())
    assert actual == {x["path"] for x in inv["owned"]} | controls
    assert digest(invbytes) == seal["inventory_sha256"]
    prebytes = (ROOT / (OLD + "prevalidation.json")).read_bytes()
    pre = json.loads(prebytes)
    assert digest(prebytes) == seal["prevalidation_sha256"]
    assert pre["status"] == "PASS" and pre["prevalidation"] is True
    assert pre["inventory_sha256"] == digest(invbytes)
    assert pre["report_sha256"] == seal["report_sha256"]
    assert pre["verifier_sha256"] == seal["verifier_sha256"]
    assert len(pre["probes"]) == 8 and all(x["blocked"] for x in pre["probes"])
    assert len(pre["comparisons"]) == 3 and all(x["byte_identical"] for x in pre["comparisons"])
    assert pre["context_before"] == pre["context_after"]
    for path in controls:
        data = (ROOT / path).read_bytes()
        bindings[path] = {"path": path, "size": len(data), "sha256": digest(data)}
    extras = [
        ROOT / "frontier/iterations/i176-uniform-five-port-rank-parent-disposition.md",
        ROOT / "frontier/iterations/iteration176-uniform-five-port-rank-brief.md",
        ROOT / "frontier/iterations/iteration177-adjacent-port-surgery-brief.md",
    ] + sorted((ROOT / "frontier/experiments").glob("i176-parent-*"))
    for path in extras:
        if path.is_file():
            data = path.read_bytes()
            rel = str(path.relative_to(ROOT))
            bindings[rel] = {"path": rel, "size": len(data), "sha256": digest(data)}
    drift = [{"path": x["path"], "historical": x["sha256"],
              "current": digest((ROOT / x["path"]).read_bytes())} for x in inv["context"]]
    return {"status": "PASS", "owned": 59, "external": 507, "contexts": drift,
            "detached": expected, "complete_membership": True,
            "control_chain": True, "opaque_ancestor_python": True,
            "bindings": sorted(bindings.values(), key=lambda x: x["path"])}


if __name__ == "__main__":
    print(json.dumps(authenticate(), indent=2, sort_keys=True))
