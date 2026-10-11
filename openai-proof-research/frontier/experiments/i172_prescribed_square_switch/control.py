"""Inventory creation, exclusive one-time sealing, and read-only byte checks."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
SOURCE = ROOT / "frontier/sources/i172_prescribed_square_switch"
REPORT = ROOT / "frontier/iterations/i172-prescribed-square-switch.md"
CONTROL = {"inventory.json", "prevalidation.json", "seal.json"}
CONTEXT = {"README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"}
REPLAYS = [
    ("mandatory", "mandatory-attempt-01.json"),
    ("populations", "populations-attempt-01.json"),
    ("remote_splices", "remote-splices-attempt-01.json"),
    ("loss_transport", "cap-transport-attempt-01.json"),
    ("cut_octagons", "cut-octagons-attempt-01.json"),
    ("residual_certificates", "residual-certificates-attempt-01.json"),
    ("cut_projection", "cut-projection-attempt-01.json"),
]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def entry(p, role):
    data = p.read_bytes()
    return dict(path=str(p.relative_to(ROOT)), size=len(data),
                sha256=sha(data), role=role)


def exclusive(p, obj):
    with p.open("x") as f:
        json.dump(obj, f, indent=2, sort_keys=True)
        f.write("\n")


def check():
    inv = json.loads((HERE / "inventory.json").read_bytes())
    counts, contexts = {}, []
    for group in ("owned", "external"):
        n = 0
        for e in inv[group]:
            data = (ROOT / e["path"]).read_bytes()
            ok = sha(data) == e["sha256"] and len(data) == e["size"]
            if e["role"] == "context-only":
                contexts.append(dict(path=e["path"], match=ok,
                                     expected=e["sha256"], actual=sha(data)))
            else:
                assert ok, e["path"]
                n += 1
        counts[group] = n
    owned = {e["path"] for e in inv["owned"]}
    actual = {str(p.relative_to(ROOT)) for directory in (HERE, SOURCE)
              for p in directory.rglob("*") if p.is_file()
              and not (p.parent == HERE and p.name in CONTROL)}
    actual.add(str(REPORT.relative_to(ROOT)))
    assert actual == owned
    return dict(status="PASS", counts=counts, contexts=contexts,
                inventory_sha256=sha((HERE / "inventory.json").read_bytes()))


def inventory():
    assert not (HERE / "seal.json").exists()
    auth = json.loads((SOURCE / "i171-authentication.json").read_bytes())
    external = {}
    for entries in auth["checks"].values():
        for e in entries:
            role = "context-only" if e["path"] in CONTEXT else "ancestor opaque bytes or mathematical data"
            actual = entry(ROOT / e["path"], role)
            if role != "context-only":
                assert actual["sha256"] == e["sha256"] and actual["size"] == e["size"]
            else:
                # Preserve the inherited comparison point, not a reset.
                actual["sha256"], actual["size"] = e["sha256"], e["size"]
            external[e["path"]] = actual
    extra = [
        "frontier/experiments/i171_square_switch_weight/inventory.json",
        "frontier/experiments/i171_square_switch_weight/prevalidation.json",
        "frontier/experiments/i171_square_switch_weight/seal.json",
        "frontier/iterations/iteration172-prescribed-square-switch-brief.md",
        "frontier/iterations/i165-square-expansion-multiplicity.md",
        "frontier/sources/i164_structural_graph_discovery/upstream-references.bib",
        "sources/preprints-tree.json",
    ]
    for name in extra:
        external[name] = entry(ROOT / name, "mathematical input or authenticated control")
    files = [p for directory in (HERE, SOURCE) for p in directory.rglob("*")
             if p.is_file() and not (p.parent == HERE and p.name in CONTROL)]
    files.append(REPORT)
    inv = dict(iteration=172, report=str(REPORT.relative_to(ROOT)),
               owned=[entry(p, "owned immutable evidence") for p in sorted(files)],
               external=[external[k] for k in sorted(external)],
               replays=[dict(function=f, payload=str((HERE / p).relative_to(ROOT)))
                        for f, p in REPLAYS],
               policy="All diagnostic data read from authenticated immutable memory; ancestor Python never executed.")
    exclusive(HERE / "inventory.json", inv)
    return check()


def seal():
    assert not (HERE / "seal.json").exists(), "never reseal"
    checks = check()
    pre = (HERE / "prevalidation.json").read_bytes()
    receipt = json.loads(pre)
    assert receipt["status"] == "PASS" and receipt["prevalidation"] is True
    assert len(receipt["comparisons"]) == len(REPLAYS)
    assert all(c["match"] for c in receipt["comparisons"])
    assert len(receipt["probes"]) == 8 and all(p["blocked"] for p in receipt["probes"])
    inventory_hash = sha((HERE / "inventory.json").read_bytes())
    report_hash = sha(REPORT.read_bytes())
    verifier_hash = sha((HERE / "verify.py").read_bytes())
    assert receipt["inventory_sha256"] == inventory_hash
    assert receipt["report_sha256"] == report_hash
    assert receipt["verifier_sha256"] == verifier_hash
    payload = dict(iteration=172, creation="exclusive-create once after successful prevalidation; never reseal",
                   inventory_sha256=inventory_hash, prevalidation_sha256=sha(pre),
                   report_sha256=report_hash, verifier_sha256=verifier_hash)
    exclusive(HERE / "seal.json", payload)
    return dict(**payload, seal_sha256=sha((HERE / "seal.json").read_bytes()), checks=checks)


if __name__ == "__main__":
    action = sys.argv[1]
    assert action in ("inventory", "seal", "check")
    print(json.dumps(globals()[action](), indent=2, sort_keys=True))
