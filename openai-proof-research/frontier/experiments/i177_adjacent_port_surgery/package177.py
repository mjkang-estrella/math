"""Build once, then exclusively seal after successful read-only prevalidation."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path("/home/mj-kang/Documents/Dev/math/openai-proof-research")
BASE = ROOT / "frontier/experiments/i177_adjacent_port_surgery"
SOURCE = ROOT / "frontier/sources/i177_adjacent_port_surgery"
REPORT = ROOT / "frontier/iterations/i177-adjacent-port-surgery.md"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def entry(path):
    data = path.read_bytes()
    return {"path": str(path.relative_to(ROOT)), "size": len(data), "sha256": sha(data)}


def exclusive(path, obj):
    with path.open("x") as f:
        json.dump(obj, f, sort_keys=True, indent=2)
        f.write("\n")


def build():
    assert not (BASE / "seal.json").exists()
    auth = json.loads((BASE / "authentication.json").read_bytes())
    external = {x["path"]: x for x in auth["bindings"]}
    # Initial strict mathematical bindings may not silently drift.
    for rel, old in external.items():
        assert entry(ROOT / rel) == old, rel
    extras = list((ROOT / "frontier/experiments").glob("i176-parent-*"))
    extras += list((ROOT / "frontier/iterations").glob("iteration17[67]-*-task.json"))
    extras += [ROOT / "AGENTS.md", ROOT / "sources/upstream.json",
               ROOT / "sources/CONTENTS.md", ROOT / "sources/preprints-tree.json"]
    for p in extras:
        if p.is_file():
            external[str(p.relative_to(ROOT))] = entry(p)
    controls = [str((BASE / n).relative_to(ROOT)) for n in
                ("inventory.json", "prevalidation.json", "seal.json")]
    owned = [REPORT] + [p for directory in (BASE, SOURCE) for p in directory.rglob("*")
                       if p.is_file() and str(p.relative_to(ROOT)) not in controls]
    contexts = []
    for c in auth["contexts"]:
        now = entry(ROOT / c["path"])
        now["I176_historical"] = c["historical"]
        now["I177_initial"] = c["current"]
        contexts.append(now)
    result = {"iteration": 177, "owned": sorted(map(entry, owned), key=lambda x: x["path"]),
              "external": sorted(external.values(), key=lambda x: x["path"]),
              "context": contexts, "controls": controls,
              "replays": [
                  {"function": "mandatory", "payload": str((BASE / "mandatory-attempt-05.json").relative_to(ROOT))},
                  {"function": "audit", "payload": str((BASE / "audit-attempt-03.json").relative_to(ROOT))},
                  {"function": "experiment", "payload": str((BASE / "experiment-attempt-03.json").relative_to(ROOT))}],
              "policy": "Immutable-first. Four historical contexts only; current bytes stable. Never reseal."}
    exclusive(BASE / "inventory.json", result)
    print(json.dumps({"owned": len(result["owned"]), "external": len(external), "contexts": 4}))


def seal():
    inv = (BASE / "inventory.json").read_bytes()
    prebytes = (BASE / "prevalidation.json").read_bytes()
    pre = json.loads(prebytes)
    assert pre["status"] == "PASS" and pre["prevalidation"]
    assert pre["inventory_sha256"] == sha(inv)
    assert pre["report_sha256"] == entry(REPORT)["sha256"]
    assert pre["verifier_sha256"] == entry(BASE / "verify177.py")["sha256"]
    assert len(pre["probes"]) == 8 and all(x["blocked"] for x in pre["probes"])
    assert len(pre["comparisons"]) == 3 and all(x["byte_identical"] for x in pre["comparisons"])
    # Recheck frozen membership and hashes immediately before the exclusive seal.
    inventory = json.loads(inv)
    for x in inventory["owned"] + inventory["external"]:
        assert entry(ROOT / x["path"]) == x
    actual = {str(REPORT.relative_to(ROOT))} | {str(p.relative_to(ROOT)) for directory in (BASE, SOURCE)
                                               for p in directory.rglob("*") if p.is_file()}
    assert actual == {x["path"] for x in inventory["owned"]} | {
        str((BASE / n).relative_to(ROOT)) for n in ("inventory.json", "prevalidation.json")}
    assert {c: entry(ROOT / c)["sha256"] for c in pre["context_after"]} == pre["context_after"]
    exclusive(BASE / "seal.json", {"iteration": 177, "inventory_sha256": sha(inv),
                                 "prevalidation_sha256": sha(prebytes),
                                 "report_sha256": pre["report_sha256"],
                                 "verifier_sha256": pre["verifier_sha256"],
                                 "creation": "One exclusive seal following successful prevalidation. Never reseal."})
    print(json.dumps({"seal_sha256": entry(BASE / "seal.json")["sha256"]}))


if __name__ == "__main__":
    {"build": build, "seal": seal}[sys.argv[1]]()
