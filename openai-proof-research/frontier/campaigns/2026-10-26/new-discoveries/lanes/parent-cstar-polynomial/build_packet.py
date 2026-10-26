#!/usr/bin/env python3
"""Build and read back the explicit, deterministic cubic polynomial proof packet.

Lean replay is a separate subsequent operation on the returned extracted path.
No generated object files or parent worktree sources are trusted after extraction.
"""
from pathlib import Path
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parents[2]
CANDIDATE = ROOT / "candidates/cstar-polynomial"
PACKET = ROOT / "candidate-packets/355008-cstar-polynomial-proof.zip"
EXTRACT = ROOT / "build/cstar-polynomial-packet-audit-v2"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    frozen = json.loads((CANDIDATE / "frozen-review-hashes.json").read_text())
    for name, digest in frozen.items():
        assert sha((CANDIDATE / name).read_bytes()) == digest, name
    names = ["README.md", "PROOF.md", "candidate.json", "main.tex", "paper.pdf",
             "frozen-review-hashes.json"]
    for folder in ["formal", "reviews", "verification", "scripts", "sources"]:
        names.extend(str(p.relative_to(CANDIDATE))
                     for p in sorted((CANDIDATE / folder).iterdir()) if p.is_file())
    assert len(names) == len(set(names))
    payload = {name: (CANDIDATE / name).read_bytes() for name in sorted(names)}
    manifest = {name: sha(value) for name, value in payload.items()}
    payload["MANIFEST.json"] = (json.dumps(manifest, indent=2) + "\n").encode()
    PACKET.parent.mkdir(exist_ok=True)
    assert not EXTRACT.exists(), "Use a new, empty extraction destination"
    with zipfile.ZipFile(PACKET, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for name, data in sorted(payload.items()):
            item = zipfile.ZipInfo("cstar-polynomial/" + name, (2026, 10, 26, 0, 0, 0))
            item.external_attr = 0o100644 << 16
            item.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(item, data, compress_type=zipfile.ZIP_DEFLATED,
                             compresslevel=9)
    with zipfile.ZipFile(PACKET) as archive:
        assert archive.testzip() is None
        assert sorted(archive.namelist()) == sorted("cstar-polynomial/" + n for n in payload)
        for name, data in payload.items():
            assert archive.read("cstar-polynomial/" + name) == data, name
        archive.extractall(EXTRACT)
    extracted = EXTRACT / "cstar-polynomial"
    read_manifest = json.loads((extracted / "MANIFEST.json").read_text())
    assert read_manifest == manifest
    for name, digest in manifest.items():
        assert sha((extracted / name).read_bytes()) == digest, name
    result = {"status": "PASS: exact archive members, byte readback and manifest hashes; Lean replay pending",
              "packet": str(PACKET.relative_to(ROOT)),
              "sha256": sha(PACKET.read_bytes()), "members": len(payload),
              "extracted": str(extracted), "frozen_hashes": frozen}
    (EXTRACT / "readback.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
