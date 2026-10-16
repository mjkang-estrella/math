#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang, no affiliation. MIT License.
"""Run the frozen package's own scripts on a disposable copy only.

The original staircase-manuscript directory is hashed before and after; the
copy is removed afterwards. Output: JSON on stdout.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
PKG = HERE.parent / "staircase-manuscript"


def tree_hashes(root):
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(root.rglob("*")) if p.is_file()}


def run(cmd, cwd):
    p = subprocess.run(cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    return {"command": cmd, "exit_code": p.returncode, "last_line": p.stdout.decode().strip().splitlines()[-1:]}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--tectonic", default="/tmp/frontier-typeset/tectonic")
    args = parser.parse_args()
    before = tree_hashes(PKG)
    result = {"original_files": len(before)}
    with tempfile.TemporaryDirectory(prefix="smr1-copy-") as folder:
        copy = Path(folder) / "pkg"
        shutil.copytree(PKG, copy)
        py = sys.executable
        result["runs"] = [
            run([py, "-B", "support/verify_package.py", "--with-inputs"], copy),
            run([py, "-B", "support/verify_package.py", "--audit-inputs-only"], copy),
            run([py, "-B", "support/reproduce.py"], copy),
            run([py, "-B", "support/build.py", "--tectonic", args.tectonic], copy),
        ]
        after_copy = tree_hashes(copy)
        result["rebuilt_pdf_sha256"] = after_copy["main.pdf"]
        result["rebuilt_pdf_identical_to_frozen"] = after_copy["main.pdf"] == before["main.pdf"]
        pages = [k for k in after_copy if k.startswith("checks/pages/")]
        result["rendered_pages"] = len(pages)
        result["page_png_identical"] = all(after_copy[k] == before.get(k) for k in pages)
        for k in ("checks/build/main.txt", "checks/input-audit.json"):
            result[k + "_identical"] = after_copy[k] == before.get(k)
        log = (copy / "checks/build/main.log").read_text(errors="replace")
        result["log_overfull"] = log.count("Overfull")
        result["log_underfull"] = log.count("Underfull")
        result["log_undefined"] = log.lower().count("undefined")
        info = subprocess.check_output(["pdfinfo", str(copy / "main.pdf")]).decode()
        result["pdfinfo"] = {l.split(":", 1)[0]: l.split(":", 1)[1].strip()
                             for l in info.splitlines() if l.split(":", 1)[0] in ("Pages", "Page size", "Title", "Author")}
        fonts = subprocess.check_output(["pdffonts", str(copy / "main.pdf")]).decode().splitlines()[2:]
        result["fonts_all_embedded"] = all(line.split()[-5] == "yes" for line in fonts if line.strip())
    after = tree_hashes(PKG)
    result["original_unchanged"] = before == after
    assert result["original_unchanged"]
    assert all(r["exit_code"] == 0 for r in result["runs"])
    assert result["rebuilt_pdf_identical_to_frozen"] and result["rendered_pages"] == 6
    result["status"] = "PASS"
    print(json.dumps(result, indent=1))


if __name__ == "__main__":
    main()
