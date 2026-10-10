"""Create the one I162 seal after read-only prevalidation; never reseal."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[3]
SREL = "frontier/sources/i162_fixed_sector_bfss_focused_astra"
EREL = "frontier/experiments/i162_fixed_sector_bfss_focused_astra"
RREL = "frontier/reviews/i162-fixed-sector-bfss-focused-astra.md"
SOURCE = ROOT / SREL


def item(rel):
    p = ROOT / rel
    if p.is_symlink():
        raise RuntimeError("symlinks forbidden")
    b = p.read_bytes()
    return {"path": rel, "bytes": len(b), "sha256": hashlib.sha256(b).hexdigest()}


def main():
    if (SOURCE / "seal.json").exists():
        raise RuntimeError("one seal only; resealing is forbidden")
    prepath = SREL + "/preseal-validation.json"
    pre = json.loads((ROOT / prepath).read_bytes())
    if pre["status"] != "PASS" or pre["mode"] != "preseal-read-only":
        raise RuntimeError("successful read-only prevalidation required")
    paths = [RREL]
    for directory in [SREL, EREL]:
        paths += [str(p.relative_to(ROOT)) for p in (ROOT / directory).rglob("*") if p.is_file()]
    current = [item(p) for p in sorted(paths)]
    # The captured stdout is the only file created between prevalidation and seal.
    if [x for x in current if x["path"] != prepath] != pre["prevalidated_inventory"]:
        raise RuntimeError("owned files changed since prevalidation")
    for x in json.loads((SOURCE / "references.json").read_bytes()):
        if item(x["path"]) != x:
            raise RuntimeError("immutable reference changed before sealing")
    digest = hashlib.sha256(json.dumps(current, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    seal = {"schema": "I162-focused-evidence-v1", "original_package_verdict": "FAIL",
            "inventory": current, "inventory_sha256": digest,
            "prevalidation_sha256": item(prepath)["sha256"],
            "scope": "One canonical inventory; not a mathematical proof or acceptance certificate"}
    with (SOURCE / "seal.json").open("x", encoding="utf-8") as output:
        json.dump(seal, output, ensure_ascii=False, indent=2)
        output.write("\n")
    print(json.dumps({"sealed_once": True, "owned_files": len(current), "inventory_sha256": digest}))


if __name__ == "__main__":
    main()
