#!/usr/bin/env python3
"""Build the manuscript with Tectonic; standard-library-only wrapper."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tectonic", default=shutil.which("tectonic"))
    parser.add_argument("--cache-dir", type=Path)
    parser.add_argument("--only-cached", action="store_true")
    args = parser.parse_args()
    if not args.tectonic:
        parser.error("Install Tectonic 0.17.0 or supply --tectonic /path/to/tectonic")
    out = ROOT / "build"
    out.mkdir(exist_ok=True)
    env = os.environ.copy()
    if args.cache_dir:
        env["XDG_CACHE_HOME"] = str(args.cache_dir.resolve())
    command = [args.tectonic, "--untrusted", "--keep-logs", "--keep-intermediates",
               "--reruns", "2", "--outdir", str(out), str(ROOT / "paper/main.tex")]
    if args.only_cached:
        command.insert(1, "--only-cached")
    run = subprocess.run(command, env=env, capture_output=True, text=True)
    (out / "tectonic.stdout").write_text(run.stdout)
    (out / "tectonic.stderr").write_text(run.stderr)
    log = (out / "main.log").read_text() if (out / "main.log").exists() else ""
    issues = [line for line in log.splitlines()
              if "Overfull" in line or "undefined" in line or line.startswith("!")]
    receipt = {"exit_code": run.returncode, "layout_or_reference_issues": issues,
               "pdf_exists": (out / "main.pdf").is_file(),
               "engine_version": subprocess.check_output(
                   [args.tectonic, "--version"], text=True).strip()}
    (out / "paper-build.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))
    if run.returncode or issues or not receipt["pdf_exists"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
