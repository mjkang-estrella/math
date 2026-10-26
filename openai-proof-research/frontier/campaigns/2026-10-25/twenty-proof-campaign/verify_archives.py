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
        root = ROOT / "build/replays" / archive.stem
        root.mkdir(parents=True, exist_ok=True)
        with zipfile.ZipFile(archive) as z:
            assert z.testzip() is None
            prefix = archive.stem + "/"
            assert all(n.startswith(prefix) and ".." not in Path(n).parts for n in z.namelist())
            expected = set()
            for line in z.read(prefix + "SHA256SUMS").decode().splitlines():
                checksum, name = line.split("  ", 1)
                assert hashlib.sha256(z.read(prefix + name)).hexdigest() == checksum
                expected.add(prefix + name)
            assert set(z.namelist()) == expected | {prefix + "SHA256SUMS"}
            z.extractall(root)
        target = root / archive.stem
        run = subprocess.run([sys.executable, str(target / "verify_outcome.py"), str(target),
                              "--lean-bin", str(a.lean_bin.resolve()),
                              "--packages", str(a.packages.resolve())], text=True, capture_output=True)
        (root / "replay.log").write_text(run.stdout + run.stderr)
        if run.returncode:
            raise RuntimeError(run.stdout + run.stderr)
        result = json.loads(run.stdout)
        return {"archive": str(archive), "sha256": hashlib.sha256(archive.read_bytes()).hexdigest(),
                "status": "PASS", "proof_sha256": result["sha256"]}

    with ThreadPoolExecutor(max_workers=min(3, len(a.archives))) as pool:
        results = list(pool.map(check, a.archives))
    a.receipt.parent.mkdir(parents=True, exist_ok=True)
    a.receipt.write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
