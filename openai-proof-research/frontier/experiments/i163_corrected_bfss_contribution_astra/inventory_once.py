"""Create the sole canonical payload inventory before read-only prevalidation."""
from pathlib import Path
import hashlib
import json

ROOT = Path("/home/mj-kang/Documents/Dev/math/openai-proof-research")
TAG = "i163_corrected_bfss_contribution_astra"
SOURCE = ROOT / "frontier/sources" / TAG
EXPERIMENT = ROOT / "frontier/experiments" / TAG
REPORT = ROOT / "frontier/reviews/i163-corrected-bfss-contribution-astra.md"
NAMES = ["inventory.json", "preseal-validation.json", "seal.json"]


def main():
    assert all(not (SOURCE / name).exists() for name in NAMES)
    paths = [REPORT]
    for parent in [SOURCE, EXPERIMENT]:
        for p in parent.rglob("*"):
            assert not p.is_symlink()
            if p.is_file():
                paths.append(p)
    rows = []
    for p in sorted(paths, key=lambda p: str(p.relative_to(ROOT))):
        data = p.read_bytes()
        rows.append({"path": str(p.relative_to(ROOT)), "bytes": len(data),
                     "sha256": hashlib.sha256(data).hexdigest()})
    result = {
        "schema": "i163-canonical-inventory-v1", "payload": rows,
        "envelope": sorted(str((SOURCE / name).relative_to(ROOT)) for name in NAMES),
        "scope": "Exact payload inventory. Seal authenticates this inventory and the prevalidation receipt; final exact owned set is payload plus these three envelope files."
    }
    with (SOURCE / "inventory.json").open("x", encoding="utf8") as f:
        json.dump(result, f, indent=2)
        f.write("\n")
    print(json.dumps({"payload_files": len(rows), "status": "INVENTORIED"}))


if __name__ == "__main__":
    main()
