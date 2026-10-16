#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT License.
"""Build copied TeX sources, save diagnostics, and render every page."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--tectonic", default="tectonic")
    args = parser.parse_args()
    compiler = shutil.which(args.tectonic)
    if compiler is None:
        raise SystemExit("Tectonic not found; pass --tectonic /path/to/tectonic")
    build = ROOT / "checks" / "build"
    pages = ROOT / "checks" / "pages"
    build.mkdir(parents=True, exist_ok=True)
    pages.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env["SOURCE_DATE_EPOCH"] = "1792022400"  # 2026-10-15 00:00:00 UTC
    with tempfile.TemporaryDirectory(prefix="build-work-", dir=ROOT / "checks") as folder:
        work = Path(folder)
        for filename in ("main.tex", "references.tex"):
            shutil.copyfile(ROOT / filename, work / filename)
        process = subprocess.run([compiler, "--keep-logs", "main.tex"], cwd=work,
                                 env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (build / "tectonic.txt").write_bytes(process.stdout)
        if (work / "main.log").exists():
            shutil.copyfile(work / "main.log", build / "main.log")
        if process.returncode:
            raise SystemExit(process.stdout.decode())
        log = (build / "main.log").read_text(errors="replace")
        assert "Overfull" not in log and "undefined" not in log.lower()
        shutil.copyfile(work / "main.pdf", ROOT / "main.pdf")
    for previous in pages.glob("page-*.png"):
        previous.unlink()
    subprocess.run(["pdftoppm", "-r", "95", "-png", str(ROOT / "main.pdf"), str(pages / "page")], check=True)
    subprocess.run(["pdftotext", "-layout", str(ROOT / "main.pdf"), str(build / "main.txt")], check=True)
    info = subprocess.check_output(["pdfinfo", str(ROOT / "main.pdf")]).decode()
    (build / "pdfinfo.txt").write_text(info)
    receipt = {"compiler": subprocess.check_output([compiler, "--version"]).decode().strip(),
               "source_date_epoch": env["SOURCE_DATE_EPOCH"],
               "pdf_sha256": hashlib.sha256((ROOT / "main.pdf").read_bytes()).hexdigest(),
               "rendered_pages": len(list(pages.glob("page-*.png"))),
               "overfull_boxes": 0, "undefined_references": 0,
               "visual_inspection": "separate manual review required after this build"}
    (build / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print("PASS: copied-source build, PDF text extraction, and every-page rendering")


if __name__ == "__main__":
    main()
