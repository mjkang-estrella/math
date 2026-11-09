#!/usr/bin/env python3
"""Rebuild local Lean sources and enforce pins and the kernel axiom allowlist.

Uses only Python's standard library, git, and the supplied Lean executable.
Dependencies must already be compiled; this script never runs Lake, downloads
packages, or modifies dependency caches. See notes/formal-audit.md for coverage.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def run(command: list[str], **kwargs: object) -> str:
    result = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, **kwargs)
    if result.returncode:
        raise RuntimeError(f"Command failed ({result.returncode}): {command!r}\n{result.stdout}")
    return result.stdout


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path,
                        default=os.environ.get("LEAN_BIN", str(HERE.parents[6] /
                        "dlp-research/.tools/lean-4.34.1-linux/bin/lean")),
                        help="Lean executable (environment: LEAN_BIN)")
    parser.add_argument("--mathlib-packages", type=Path,
                        default=os.environ.get("MATHLIB_PACKAGES", str(HERE.parents[3] /
                        "2026-10-14/formal/.lake/packages")),
                        help="Directory containing compiled mathlib and its dependencies "
                        "(environment: MATHLIB_PACKAGES)")
    args = parser.parse_args()
    # A failed rebuild must not leave an earlier success certificate in place.
    (HERE / "build/audit.json").unlink(missing_ok=True)
    lean = args.lean_bin.expanduser().resolve(strict=True)
    packages = args.mathlib_packages.expanduser().resolve(strict=True)
    pins = json.loads((HERE / "pins.json").read_text())
    version = run([str(lean), "--version"]).strip()
    if not re.search(r"\bversion " + re.escape(pins["lean_version"]) + r"(?:\s|,|$)", version):
        raise RuntimeError(f"Wrong Lean version: {version}")
    if (HERE / "lean-toolchain").read_text().strip() != "leanprover/lean4:v" + pins["lean_version"]:
        raise RuntimeError("Local lean-toolchain disagrees with pins.json")
    revisions = {"mathlib": pins["mathlib_revision"], **pins["dependencies"]}
    libraries = []
    for name, expected in revisions.items():
        package = packages / name
        actual = run(["git", "-C", str(package), "rev-parse", "HEAD"]).strip()
        if actual != expected:
            raise RuntimeError(f"Revision mismatch for {name}: {actual} != {expected}")
        dirty = run(["git", "-C", str(package), "status", "--porcelain", "--untracked-files=no"])
        if dirty.strip():
            raise RuntimeError(f"Tracked changes in pinned dependency {name}:\n{dirty}")
        library = package / ".lake/build/lib/lean"
        if name == "mathlib" and not library.is_dir():
            raise RuntimeError(f"Missing compiled mathlib: {library}")
        # Include every dependency path; unused tools such as Cli may have no
        # library cache. Lean reports any actually required missing artifact.
        libraries.append(library)
    manifest = json.loads((packages / "mathlib/lake-manifest.json").read_text())
    manifest_revisions = {p["name"]: p["rev"] for p in manifest["packages"]}
    if manifest_revisions != pins["dependencies"]:
        raise RuntimeError("Mathlib manifest disagrees with dependency pins")

    source = (HERE / "Monochromatic.lean").read_text()
    declarations = re.findall(r"^(?:noncomputable )?(?:def|theorem)\s+(\w+)", source, flags=re.MULTILINE)
    if len(declarations) != len(set(declarations)):
        raise RuntimeError("Duplicate local declaration names")
    checks = (HERE / "Checks.lean").read_text()
    for directive in ("#check", "#print axioms"):
        found = re.findall(re.escape(directive) + r"\s+MonochromaticBox\.(\w+)", checks)
        if sorted(found) != sorted(declarations):
            raise RuntimeError(f"Incomplete/duplicate declaration coverage for {directive}")
    for path in (HERE / "Monochromatic.lean", HERE / "Checks.lean"):
        if re.search(r"\b(sorry|admit|native_decide|axiom)\b", path.read_text()):
            raise RuntimeError(f"Forbidden proof token in {path.name}")

    # The source directory is deliberately NOT on LEAN_PATH. In particular, the
    # old Monochromatic.olean adjacent to the source cannot satisfy Checks' import.
    build = HERE / "build"
    build.mkdir(exist_ok=True)
    for name in ("Monochromatic", "Checks"):
        for suffix in (".olean", ".ilean", ".olean.private", ".olean.server"):
            (build / (name + suffix)).unlink(missing_ok=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(map(str, [build, *libraries]))
    for name in ("Monochromatic", "Checks"):
        command = [str(lean), "-DwarningAsError=true", "-o", str(build / (name + ".olean")),
                   str(HERE / (name + ".lean"))]
        try:
            output = run(command, cwd=HERE, env=env)
        except RuntimeError as error:
            (build / (name + ".log")).write_text(str(error) + "\n")
            raise
        (build / (name + ".log")).write_text(output)
        if output:
            print(output, end="")
    reports = re.findall(
        r"'MonochromaticBox\.(\w+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",
        output, re.DOTALL)
    if sorted(name for name, _ in reports) != sorted(declarations):
        raise RuntimeError("Incomplete axiom reports from Lean")
    observed: set[str] = set()
    for name, text in reports:
        axioms = {a.strip() for a in text.split(",") if a.strip()}
        unexpected = axioms - ALLOWED_AXIOMS
        if unexpected:
            raise RuntimeError(f"Unexpected axioms in {name}: {sorted(unexpected)}")
        observed |= axioms
    record = {
        "lean": version, "pins": pins, "declarations_checked": len(declarations),
        "axioms_observed": sorted(observed), "lean_path": env["LEAN_PATH"],
        "sources": {},
    }
    import hashlib
    for name in ("Monochromatic.lean", "Checks.lean", "rebuild.py", "pins.json", "lean-toolchain"):
        record["sources"][name] = hashlib.sha256((HERE / name).read_bytes()).hexdigest()
    (build / "audit.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"PASS: rebuilt and audited {len(declarations)} declarations; "
          f"axioms: {', '.join(sorted(observed)) or '(none)'}. Logs: {build}")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        sys.exit(1)
