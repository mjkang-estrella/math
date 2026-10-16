#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT License (see LICENSE-CODE).
"""Build main.tex in a scratch copy, save diagnostics, and render every page.

Requires Tectonic and Poppler (pdftoppm, pdftotext, pdfinfo). Tectonic runs
with --only-cached so that no network access or cache writes are needed when
its package cache is already populated.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--tectonic", default="tectonic")
    parser.add_argument("--allow-network", action="store_true",
                        help="let Tectonic download missing packages")
    args = parser.parse_args()
    compiler = shutil.which(args.tectonic)
    if compiler is None:
        sys.exit("Tectonic not found; pass --tectonic /path/to/tectonic")
    build = ROOT / "checks" / "build"
    pages = ROOT / "checks" / "pages"
    work = ROOT / "checks" / "work-build"
    for folder in (build, pages, work):
        if folder.exists():
            shutil.rmtree(folder)
        folder.mkdir(parents=True)
    shutil.copyfile(ROOT / "main.tex", work / "main.tex")
    env = dict(os.environ)
    env["SOURCE_DATE_EPOCH"] = "1792108800"  # 2026-10-16 00:00:00 UTC
    cmd = [compiler, "--keep-logs"] + ([] if args.allow_network else ["--only-cached"]) + ["main.tex"]
    proc = subprocess.run(cmd, cwd=work, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (build / "tectonic.txt").write_bytes(proc.stdout)
    if (work / "main.log").exists():
        shutil.copyfile(work / "main.log", build / "main.log")
    if proc.returncode:
        sys.exit(proc.stdout.decode(errors="replace"))
    log = (build / "main.log").read_text(errors="replace")
    problems = {
        "overfull_boxes": len(re.findall(r"^Overfull", log, re.M)),
        "underfull_boxes": len(re.findall(r"^Underfull", log, re.M)),
        "undefined_references_or_citations": len(re.findall(r"undefined", log, re.I)),
        "rerun_warnings": len(re.findall(r"Rerun to get", log)),
    }
    shutil.copyfile(work / "main.pdf", ROOT / "main.pdf")
    shutil.rmtree(work)
    subprocess.run(["pdftoppm", "-r", "100", "-png", str(ROOT / "main.pdf"), str(pages / "page")], check=True)
    subprocess.run(["pdftotext", "-layout", str(ROOT / "main.pdf"), str(build / "main.txt")], check=True)
    info = subprocess.check_output(["pdfinfo", str(ROOT / "main.pdf")]).decode()
    (build / "pdfinfo.txt").write_text(info)
    receipt = {
        "compiler": subprocess.check_output([compiler, "--version"]).decode().strip(),
        "command": " ".join(Path(c).name if i == 0 else c for i, c in enumerate(cmd)),
        "source_date_epoch": env["SOURCE_DATE_EPOCH"],
        "main_tex_sha256": hashlib.sha256((ROOT / "main.tex").read_bytes()).hexdigest(),
        "pdf_sha256": hashlib.sha256((ROOT / "main.pdf").read_bytes()).hexdigest(),
        "pdf_pages": int(re.search(r"Pages:\s+(\d+)", info).group(1)),
        "rendered_pages": len(list(pages.glob("page-*.png"))),
        "log_findings": problems,
        "visual_inspection": "manual; see checks/visual-review.json",
    }
    (build / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    if problems["overfull_boxes"] or problems["undefined_references_or_citations"] or problems["rerun_warnings"]:
        sys.exit(f"BUILD FAILED: {problems}")
    print(f"BUILD PASSED: {receipt['pdf_pages']} pages, findings {problems}")


if __name__ == "__main__":
    main()
