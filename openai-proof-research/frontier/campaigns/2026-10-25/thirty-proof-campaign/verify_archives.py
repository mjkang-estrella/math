#!/usr/bin/env python3
"""Check our release archives and rebuild each proof from an extracted copy."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import zipfile
import tempfile
from collect_release import validate_members

ROOT = Path(__file__).resolve().parent


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("archives", nargs="+", type=Path)
    p.add_argument("--lean-bin", type=Path, default=Path("/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean"))
    p.add_argument("--packages", type=Path, default=ROOT.parent.parent / "2026-10-14/formal/.lake/packages")
    p.add_argument("--receipt", type=Path, default=ROOT / "build/archive-replays.json")
    a = p.parse_args()

    def check(archive):
        archive = archive.resolve()
        replay_parent = ROOT / "build/replays"
        replay_parent.mkdir(parents=True, exist_ok=True)
        root = Path(tempfile.mkdtemp(prefix=archive.stem + "-", dir=replay_parent))
        with zipfile.ZipFile(archive) as z:
            if z.testzip() is not None:
                raise RuntimeError("Archive CRC check failed")
            prefix = validate_members(z)
            if prefix != archive.stem + "/":
                raise RuntimeError("Archive root does not match archive name")
            z.extractall(root)
        target = root / archive.stem
        run = subprocess.run([sys.executable, str(target / "verify_outcome.py"), str(target),
                              "--lean-bin", str(a.lean_bin.resolve()),
                              "--packages", str(a.packages.resolve())], text=True, capture_output=True)
        (root / "replay.log").write_text(run.stdout + run.stderr)
        if run.returncode:
            raise RuntimeError(run.stdout + run.stderr)
        result = json.loads(run.stdout)
        meta = json.loads((target / "outcome.json").read_text())
        expected_theorem = meta["namespace"] + "." + meta["main_theorem"]
        proof = target / "formal" / (meta["module"] + ".lean")
        if (result.get("status") != "PASS" or result.get("main_theorem") != expected_theorem or
                result.get("declarations") != meta.get("formal_declarations") or
                result.get("sha256") != hashlib.sha256(proof.read_bytes()).hexdigest()):
            raise RuntimeError("Fresh replay receipt does not bind the accepted source and theorem")
        return {"archive": str(archive), "sha256": hashlib.sha256(archive.read_bytes()).hexdigest(),
                "status": "PASS", "proof_sha256": result["sha256"]}

    with ThreadPoolExecutor(max_workers=min(3, len(a.archives))) as pool:
        results = list(pool.map(check, a.archives))
    a.receipt.parent.mkdir(parents=True, exist_ok=True)
    a.receipt.write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
