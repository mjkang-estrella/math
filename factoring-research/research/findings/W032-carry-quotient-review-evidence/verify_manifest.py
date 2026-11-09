"""Read-only integrity verification. Does not execute any research algorithm."""

from pathlib import Path
import hashlib
import json


EVIDENCE = Path(__file__).resolve().parent
ROOT = EVIDENCE.parents[2]
REPORT = ROOT / "research/findings/W032-carry-quotient-review.md"
MANIFEST = EVIDENCE / "manifest.json"


def digest(path):
    data = path.read_bytes()
    return len(data), hashlib.sha256(data).hexdigest()


def check_entry(path, entry):
    assert path.is_file() and not path.is_symlink(), str(path)
    size, sha = digest(path)
    assert size == entry["bytes"], f"Byte-count mismatch: {path}"
    assert sha == entry["sha256"], f"Hash mismatch: {path}"


def main():
    manifest = json.loads(MANIFEST.read_text())
    expected = {REPORT}
    expected.update(p for p in EVIDENCE.rglob("*") if p.is_file() and p != MANIFEST)
    entries = manifest["payloads"]
    listed = set()
    for entry in entries:
        path = ROOT / entry["path"]
        assert path == REPORT or path.is_relative_to(EVIDENCE), entry["path"]
        assert path.resolve() == path, entry["path"]
        assert path not in listed, f"Duplicate manifest path: {path}"
        listed.add(path)
        check_entry(path, entry)
    assert listed == expected, {
        "unlisted": sorted(str(p) for p in expected - listed),
        "missing": sorted(str(p) for p in listed - expected),
    }

    frozen = json.loads((EVIDENCE / "input-manifest.json").read_text())
    for entry in frozen["inputs"]:
        check_entry(EVIDENCE / entry["frozen"], entry)
    check_entry(EVIDENCE / frozen["brief"]["path"], frozen["brief"])

    sources = json.loads((EVIDENCE / "source-manifest.json").read_text())
    for entry in sources["sources"]:
        check_entry(EVIDENCE / entry["file"], entry)

    print(json.dumps({
        "status": "PASS",
        "payload_count": len(entries),
        "frozen_local_input_count": len(frozen["inputs"]),
        "frozen_external_source_count": len(sources["sources"]),
        "brief_hash_verified": True,
        "complete_owned_file_set_verified": True,
        "manifest_sha256": digest(MANIFEST)[1],
        "report_sha256": digest(REPORT)[1],
        "scope": "File integrity only; no numerical or symbolic research computation.",
    }, indent=2))


if __name__ == "__main__":
    main()
