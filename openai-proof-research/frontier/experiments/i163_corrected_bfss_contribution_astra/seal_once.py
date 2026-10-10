"""Create one seal only after successful immutable-first read-only prevalidation."""
from pathlib import Path
import hashlib
import json

ROOT = Path("/home/mj-kang/Documents/Dev/math/openai-proof-research")
SOURCE = ROOT / "frontier/sources/i163_corrected_bfss_contribution_astra"
EXPERIMENT = ROOT / "frontier/experiments/i163_corrected_bfss_contribution_astra"
REPORT = ROOT / "frontier/reviews/i163-corrected-bfss-contribution-astra.md"


def record(p):
    data = p.read_bytes()
    return {"path": str(p.relative_to(ROOT)), "bytes": len(data),
            "sha256": hashlib.sha256(data).hexdigest()}


def main():
    assert not (SOURCE / "seal.json").exists()
    inventory = json.loads((SOURCE / "inventory.json").read_text())
    pre = json.loads((SOURCE / "preseal-validation.json").read_text())
    assert pre["status"] == "PASS" and pre["mode"] == "prevalidate-read-only"
    assert pre["inventory"] == record(SOURCE / "inventory.json")
    assert pre["all_immutable_checks_before_diagnostics"] is True
    for row in inventory["payload"]:
        assert record(ROOT / row["path"]) == row, row["path"]
    current = [REPORT] + [p for folder in [SOURCE, EXPERIMENT] for p in folder.rglob("*") if p.is_file()]
    assert all(not p.is_symlink() for p in current)
    expected = {r["path"] for r in inventory["payload"]}
    expected |= {str((SOURCE / name).relative_to(ROOT)) for name in [
        "inventory.json", "preseal-validation.json"]}
    assert {str(p.relative_to(ROOT)) for p in current} == expected
    seal = {
        "schema": "i163-one-seal-v1",
        "inventory": record(SOURCE / "inventory.json"),
        "prevalidation": record(SOURCE / "preseal-validation.json"),
        "recommendation": "TECHNICAL ONLY, corrected entire theorem",
        "original_exact_operator": "FAIL retained; separate source coefficient i/2 correction",
        "scope": "Single final evidence seal, not mathematical or acceptance certification."
    }
    with (SOURCE / "seal.json").open("x", encoding="utf8") as f:
        json.dump(seal, f, indent=2)
        f.write("\n")
    print(json.dumps(record(SOURCE / "seal.json"), indent=2))


if __name__ == "__main__":
    main()
