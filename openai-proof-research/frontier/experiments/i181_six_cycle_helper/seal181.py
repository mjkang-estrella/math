from __future__ import annotations

import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
BASE = ROOT / "frontier/experiments/i181_six_cycle_helper"
REPORT = ROOT / "frontier/iterations/i181-six-cycle-helper.md"
INVENTORY = BASE / "inventory.json"
PREVALIDATION = BASE / "prevalidation.json"
VERIFIER = BASE / "verify181.py"
SEAL = BASE / "seal.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    if SEAL.exists():
        raise RuntimeError("the exclusive I181 seal already exists")
    inventory = json.loads(INVENTORY.read_text(encoding="utf-8"))
    prevalidation = json.loads(PREVALIDATION.read_text(encoding="utf-8"))
    if prevalidation.get("status") != "PASS":
        raise RuntimeError("prevalidation has not passed")
    for entry in inventory["files"]:
        path = ROOT / entry["path"]
        if sha256(path) != entry["sha256"]:
            raise RuntimeError(f"inventory mismatch before sealing: {entry['path']}")
    payload = {
        "package": "I181",
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "report_sha256": sha256(REPORT),
        "inventory_sha256": sha256(INVENTORY),
        "prevalidation_sha256": sha256(PREVALIDATION),
        "verifier_sha256": sha256(VERIFIER),
        "inventory_file_count": inventory["file_count"],
        "mandatory_payload_sha256": "29c2240943d5f45b2ad44558e6c2fea9012d31e2823a157844c121d908f6aa94",
        "topology_payload_sha256": "4c0ab64811a25094a5f001466695a036128742bb07a39e2e70afcd148b38320f",
        "exclusive_roots": inventory["exclusive_roots"],
    }
    with SEAL.open("x", encoding="utf-8") as handle:
        handle.write(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"seal": "CREATED", "sha256": sha256(SEAL)}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
