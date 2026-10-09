"""Verify the frozen I14 R2 dependency and output seal, without writing files."""
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parents[3]
source = root / "frontier/sources/i14_spectral_width_r2"
seal = json.loads((source / "artifact-seal.json").read_text())
for row in seal["artifacts"]:
    data = (root / row["path"]).read_bytes()
    assert len(data) == row["bytes"], row["path"]
    assert hashlib.sha256(data).hexdigest() == row["sha256"], row["path"]
canonical = json.dumps(seal["artifacts"], sort_keys=True, separators=(",", ":")).encode()
assert hashlib.sha256(canonical).hexdigest() == seal["artifact_list_sha256"]
inputs = json.loads((source / "input-manifest.json").read_text())
for row in inputs["files"]:
    assert hashlib.sha256((root / row["snapshot"]).read_bytes()).hexdigest() == row["sha256"]
review = root / "frontier/reviews/i14-sharp-spectral-width-r2.md"
assert seal["candidate_sha256"] in review.read_text()
print(json.dumps({
    "status": "PASS",
    "sealed_artifacts": len(seal["artifacts"]),
    "frozen_inputs": len(inputs["files"]),
    "seal_sha256": hashlib.sha256((source / "artifact-seal.json").read_bytes()).hexdigest(),
}))
