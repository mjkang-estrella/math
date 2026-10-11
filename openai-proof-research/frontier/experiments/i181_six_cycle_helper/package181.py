from __future__ import annotations

import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
BASE = ROOT / "frontier/experiments/i181_six_cycle_helper"
REPORT = ROOT / "frontier/iterations/i181-six-cycle-helper.md"
SOURCE = ROOT / "frontier/sources/i181_six_cycle_helper"
OUT = BASE / "inventory.json"
EXCLUDED = {"inventory.json", "prevalidation.json", "seal.json"}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def owned_files() -> list[Path]:
    files: list[Path] = [REPORT]
    files.extend(sorted(p for p in SOURCE.rglob("*") if p.is_file()))
    files.extend(
        p for p in sorted(BASE.rglob("*"))
        if p.is_file() and p.name not in EXCLUDED
    )
    for path in files:
        if path.is_symlink():
            raise ValueError(f"symlink is not owned evidence: {path}")
        resolved = path.resolve()
        if resolved != REPORT and BASE not in resolved.parents and SOURCE not in resolved.parents:
            raise ValueError(f"outside exclusive I181 roots: {path}")
    return files


def main() -> None:
    if (BASE / "seal.json").exists():
        raise RuntimeError("seal already exists; refusing to rebuild inventory")
    files = owned_files()
    entries = []
    for path in files:
        rel = path.relative_to(ROOT).as_posix()
        entries.append({
            "path": rel,
            "sha256": sha256(path),
            "size": path.stat().st_size,
        })
    payload = {
        "package": "I181",
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "exclusive_roots": [
            REPORT.relative_to(ROOT).as_posix(),
            (BASE.relative_to(ROOT) / "").as_posix(),
            (SOURCE.relative_to(ROOT) / "").as_posix(),
        ],
        "file_count": len(entries),
        "files": entries,
        "excluded_generated_files": sorted(EXCLUDED),
    }
    OUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({
        "inventory": str(OUT),
        "file_count": len(entries),
        "sha256": sha256(OUT),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
