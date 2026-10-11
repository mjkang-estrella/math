"""Fresh byte-only authentication. Ancestor Python is never interpreted."""
import hashlib
import json
from pathlib import Path

ROOT = Path("/home/mj-kang/Documents/Dev/math/openai-proof-research")
HERE = ROOT / "frontier/experiments/i180_survivor_helper_connectivity"
OLD = "frontier/experiments/i179_path_recombination/"
CONTEXT = ["README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"]
ANCHORS = {
    "frontier/iterations/i179-path-recombination.md":
        "de1b82735be4839890d6ce76f646db237822da617d6c33ae8564187b17390f12",
    OLD + "seal.json":
        "b73cf2bee6ec06003a85c7741cc29164b23949b6fe815413c8420e6f3a57d366",
    OLD + "verify179.py":
        "8ebcb120ed0762c4e7d75e7500833d36dd3c8d4f050784f3c1217de1fe099593",
}


def digest(b):
    return hashlib.sha256(b).hexdigest()


def record(p):
    f = ROOT / p
    assert f.is_file() and not f.is_symlink(), p
    b = f.read_bytes()
    return {"path": p, "sha256": digest(b), "size": len(b)}


def load(p):
    return json.loads((ROOT / p).read_bytes())


def encoded(x):
    return (json.dumps(x, sort_keys=True, indent=2) + "\n").encode()


def exclusive(p, data):
    with p.open("xb") as f:
        f.write(data)


def membership(stem, report):
    paths = {report}
    for sub in ("experiments", "sources"):
        directory = ROOT / ("frontier/" + sub + "/" + stem)
        assert directory.is_dir()
        for f in directory.rglob("*"):
            assert not f.is_symlink(), f
            if f.is_file():
                paths.add(str(f.relative_to(ROOT)))
    return paths


def authenticate():
    for p, h in ANCHORS.items():
        assert record(p)["sha256"] == h, p
    inv = load(OLD + "inventory.json")
    seal = load(OLD + "seal.json")
    pre = load(OLD + "prevalidation.json")
    assert (len(inv["owned"]), len(inv["external"]), len(inv["context"])) == (122, 774, 4)
    assert sorted(x["path"] for x in inv["context"]) == sorted(CONTEXT)
    for section in ("owned", "external"):
        assert len({x["path"] for x in inv[section]}) == len(inv[section])
        for entry in inv[section]:
            assert record(entry["path"]) == entry, entry["path"]
    expected = {v["path"] for v in inv["owned"]} | set(inv["controls"])
    assert membership("i179_path_recombination",
                      "frontier/iterations/i179-path-recombination.md") == expected
    assert seal["inventory_sha256"] == record(OLD + "inventory.json")["sha256"]
    assert seal["prevalidation_sha256"] == record(OLD + "prevalidation.json")["sha256"]
    assert pre["status"] == "PASS" and pre["prevalidation"]
    assert pre["inventory_sha256"] == seal["inventory_sha256"]
    assert pre["report_sha256"] == seal["report_sha256"]
    assert pre["verifier_sha256"] == seal["verifier_sha256"]
    assert all(c["byte_identical"] for c in pre["comparisons"])
    assert len(pre["probes"]) == 8 and all(p["blocked"] for p in pre["probes"])
    original = load(OLD + "inputs.json")
    supplement = load(OLD + "supplement.json")
    assert len(original["strict"]) == 773 and len(supplement["strict"]) == 1
    assert supplement["original_inputs_sha256"] == record(OLD + "inputs.json")["sha256"]
    assert sorted(original["strict"] + supplement["strict"], key=lambda e: e["path"]) == inv["external"]
    for replay, check in zip(inv["replays"], pre["comparisons"]):
        assert replay["function"] == check["function"]
        assert record(replay["payload"])["sha256"] == check["sha256"]
    # The entire inherited I178 membership and its control chain are also bound.
    prefix = "frontier/experiments/i178_five_port_annihilator/"
    ancestor = load(prefix + "inventory.json")
    assert membership("i178_five_port_annihilator",
                      "frontier/iterations/i178-five-port-annihilator.md") == (
                          {x["path"] for x in ancestor["owned"]} | set(ancestor["controls"]))
    a_seal = load(prefix + "seal.json")
    for name in ("inventory", "prevalidation"):
        assert a_seal[name + "_sha256"] == record(prefix + name + ".json")["sha256"]
    assert load(prefix + "prevalidation.json")["status"] == "PASS"
    assert load(prefix + "inputs.json")["strict"] == ancestor["external"]
    return inv, {
        "status": "PASS", "owned": 122, "strict_external": 774, "contexts": 4,
        "I179_membership": True, "I178_membership": True,
        "control_chain": True, "original_773_plus_1": True,
        "ancestor_python": "opaque bytes only",
    }


def frozen():
    data = json.loads((HERE / "inputs.json").read_bytes())
    for item in data["strict"]:
        assert record(item["path"]) == item, item["path"]
    for item in data["context"]:
        assert record(item["path"]) == {k: item[k] for k in ("path", "sha256", "size")}
    authenticate()
    return data


def freeze():
    inv, receipt = authenticate()
    paths = {e["path"] for e in inv["external"] + inv["owned"]} | set(inv["controls"])
    additions = list((ROOT / "frontier/experiments").glob("i179-parent-*"))
    additions += list((ROOT / "frontier/iterations").glob("iteration179-path-recombination-*"))
    additions += list((ROOT / "frontier/iterations").glob("iteration180-survivor-helper-connectivity-*"))
    additions += [ROOT / "frontier/iterations/i179-path-recombination-parent-disposition.md"]
    paths.update(str(p.relative_to(ROOT)) for p in additions if p.is_file())
    assert "frontier/experiments/i179-parent-integration.json" in paths
    data = {
        "status": "PASS", "authentication": receipt,
        "policy": "Exclusive immutable complete input freeze before any I180 mathematics.",
        "detached_anchors": ANCHORS,
        "strict": [record(p) for p in sorted(paths)],
        "context": [dict(record(p), inherited=next(e["sha256"] for e in inv["context"]
                                                  if e["path"] == p)) for p in CONTEXT],
        "late_receipt": "I179 final integration receipt arrived during source reading, before freeze.",
        "missing_at_freeze": [],
    }
    exclusive(HERE / "inputs.json", encoded(data))
    print(json.dumps({"status": "PASS", "strict": len(paths), "contexts": 4,
                      "inputs_sha256": record(str((HERE / "inputs.json").relative_to(ROOT)))["sha256"]}))


if __name__ == "__main__":
    freeze()
