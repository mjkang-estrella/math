#!/usr/bin/env python3
"""Build a campaign paper and reject TeX errors, missing references or overflow."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("outcome", type=Path)
    p.add_argument("--tectonic", required=True, type=Path)
    p.add_argument("--cache-dir", type=Path, default=ROOT / "build/cache")
    p.add_argument("--only-cached", action="store_true")
    a = p.parse_args()
    target = a.outcome.resolve()
    build = target / "build"
    build.mkdir(exist_ok=True)
    cmd = [str(a.tectonic.resolve()), "--untrusted", "--keep-logs", "--reruns", "2",
           "--outdir", str(build), str(target / "main.tex")]
    if a.only_cached:
        cmd.insert(1, "--only-cached")
    proc = subprocess.run(cmd, env=dict(os.environ, XDG_CACHE_HOME=str(a.cache_dir.resolve())),
                          text=True, capture_output=True)
    (build / "paper-build.log").write_text(proc.stdout + proc.stderr)
    log = (build / "main.log").read_text() if (build / "main.log").exists() else ""
    errors = [s for s in log.splitlines() if "Overfull" in s or "undefined" in s or s.startswith("!")]
    result = {"exit_code": proc.returncode, "issues": errors,
              "pdf_exists": (build / "main.pdf").is_file(),
              "tex_sha256": hashlib.sha256((target / "main.tex").read_bytes()).hexdigest()}
    (build / "paper-build.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    if proc.returncode or errors or not result["pdf_exists"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
