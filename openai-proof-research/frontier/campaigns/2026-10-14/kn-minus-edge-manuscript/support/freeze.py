#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT License (see LICENSE-CODE).
"""Freeze the inspected package: public manifest, deterministic public ZIP,
output manifest and SHA256SUMS. Refuses to run unless the recorded runs,
build receipt and visual review match the current main.tex and main.pdf."""
import hashlib
import json
from pathlib import Path
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[1]
ZIP_NAME = "kn-minus-edge-manuscript-public.zip"
FORBIDDEN_PREFIXES = ("work/", "checks/pages/", "checks/work-")


def entry(path):
    data = (ROOT / path).read_bytes()
    return {"path": path, "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def load(path):
    return json.loads((ROOT / path).read_text())


def save(name, value):
    (ROOT / name).write_text(json.dumps(value, indent=2) + "\n")


def preconditions():
    problems = []
    tex, pdf = entry("main.tex")["sha256"], entry("main.pdf")["sha256"]
    build = load("checks/build/receipt.json")
    if build["main_tex_sha256"] != tex or build["pdf_sha256"] != pdf:
        problems.append("build receipt does not match main.tex/main.pdf")
    if any(build["log_findings"][k] for k in ("overfull_boxes", "undefined_references_or_citations", "rerun_warnings")):
        problems.append("build receipt has blocking findings")
    visual = load("checks/visual-review.json")
    if visual["status"] != "PASS" or visual["pdf_sha256"] != pdf or visual["main_tex_sha256"] != tex:
        problems.append("visual review missing, failing, or for a different build")
    if visual["pages_inspected"] != build["pdf_pages"]:
        problems.append("not every page inspected")
    for name in ("checks/run-receipt.json", "checks/run-receipt-large.json"):
        receipt = load(name)
        if receipt["status"] != "PASS" or receipt["failures"]:
            problems.append(f"{name} is not PASS")
        if receipt["runner_sha256"] != entry("support/run_all.py")["sha256"]:
            problems.append(f"{name} was produced by a different runner")
    return problems


def main():
    problems = preconditions()
    public = load("public-files.json")["files"]
    if len(public) != len(set(public)) or "public-manifest.json" in public:
        problems.append("public allowlist has duplicates or lists its own manifest")
    for path in public:
        if path.startswith(FORBIDDEN_PREFIXES) or ".." in Path(path).parts or not (ROOT / path).is_file():
            problems.append(f"bad public path {path}")
    if problems:
        sys.exit("FREEZE REFUSED:\n  " + "\n  ".join(problems))

    save("public-manifest.json", {
        "schema": 1, "rights": "RIGHTS.md",
        "excluded": ["work/**", "checks/pages/**", "all third-party reading copies (referenced by hash in input-manifest.json)"],
        "self_hash_excluded": True, "files": [entry(path) for path in public]})
    with zipfile.ZipFile(ROOT / ZIP_NAME, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in public + ["public-manifest.json"]:
            info = zipfile.ZipInfo(path, date_time=(2026, 10, 16, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, (ROOT / path).read_bytes())

    outputs = sorted(str(path.relative_to(ROOT)) for path in ROOT.rglob("*")
                     if path.is_file() and path.name not in ("output-manifest.json", "SHA256SUMS")
                     and "__pycache__" not in path.parts)
    save("output-manifest.json", {
        "schema": 1, "scope": "complete local handoff directory; a provenance record, not a redistribution grant",
        "excluded_from_this_manifest": ["output-manifest.json", "SHA256SUMS", "__pycache__/**"],
        "local_only_not_public": ["work/chn-v5.txt (text extraction of a third-party survey)", "work/release-trial.json (early trial receipt)"],
        "files": [entry(path) for path in outputs]})
    (ROOT / "SHA256SUMS").write_text("".join(entry(path)["sha256"] + "  " + path + "\n"
                                         for path in outputs + ["output-manifest.json"]))
    print(f"Frozen: {len(public)} public files; {len(outputs)} handoff files")


if __name__ == "__main__":
    main()
