#!/usr/bin/env python3
"""Compile and audit one self-contained outcome against the pinned dependencies."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def run(command, **kwargs):
    p = subprocess.run(list(map(str, command)), text=True, capture_output=True, **kwargs)
    if p.returncode:
        raise RuntimeError(p.stdout + p.stderr)
    return p.stdout + p.stderr


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("outcome", type=Path)
    p.add_argument("--lean-bin", type=Path, default=os.environ.get("LEAN_BIN",
        "/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean"))
    p.add_argument("--packages", type=Path, default=os.environ.get("MATHLIB_PACKAGES",
        str(ROOT.parent.parent / "2026-10-14/formal/.lake/packages")))
    a = p.parse_args()
    outcome = a.outcome.resolve()
    manifest = json.loads((outcome / "outcome.json").read_text())
    pins = json.loads((ROOT / "pins.json").read_text())
    module, namespace = manifest["module"], manifest["namespace"]
    if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", module + namespace):
        raise RuntimeError("Invalid module or namespace name")
    build = outcome / "build"
    build.mkdir(exist_ok=True)
    (build / "audit.json").unlink(missing_ok=True)
    version = run([a.lean_bin, "--version"])
    if "version " + pins["lean_version"] + "," not in version:
        raise RuntimeError("Wrong compiler: " + version)
    packages = a.packages.resolve()
    deps = {"mathlib": pins["mathlib_revision"], **pins["dependencies"]}
    for name, expected in deps.items():
        actual = run(["git", "-C", packages / name, "rev-parse", "HEAD"]).strip()
        if actual != expected:
            raise RuntimeError("Wrong dependency revision: " + name)
        if run(["git", "-C", packages / name, "status", "--porcelain", "--untracked-files=no"]).strip():
            raise RuntimeError("Modified dependency: " + name)
    source = outcome / "formal" / (module + ".lean")
    text = source.read_text()
    if re.search(r"\b(sorry|admit|native_decide|axiom|unsafe)\b", text):
        raise RuntimeError("Forbidden proof token")
    names = re.findall(r"^(?:noncomputable )?(?:abbrev|def|theorem|lemma)\s+(\w+)", text, re.M)
    # Named generated instances can be listed explicitly, so their types and
    # axioms receive the same audit as the mathematical declarations.
    extra = manifest.get("extra_declarations", [])
    if not all(isinstance(n, str) and re.fullmatch(r"[A-Za-z_]\w*", n) for n in extra):
        raise RuntimeError("Invalid extra declaration inventory")
    names += extra
    if not names or len(names) != len(set(names)) or manifest["main_theorem"] not in names:
        raise RuntimeError("Incomplete or ambiguous declaration inventory")
    checks = "import " + module + "\n\n" + "\n".join(
        f"#check {namespace}.{n}\n#print axioms {namespace}.{n}" for n in names) + "\n"
    # Compile a byte-identical isolated source copy so both generated modules
    # share one Lean module root and no stale source-adjacent object is used.
    copied_source = build / (module + ".lean")
    copied_source.write_text(text)
    (build / "Checks.lean").write_text(checks)
    for name in (module, "Checks"):
        (build / (name + ".olean")).unlink(missing_ok=True)
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str,
        [build] + [packages / n / ".lake/build/lib/lean" for n in deps])))
    for name, path in ((module, copied_source), ("Checks", build / "Checks.lean")):
        log = run([a.lean_bin, "-DwarningAsError=true", "-o", build / (name + ".olean"), path],
                  cwd=build, env=env)
        (build / (name + ".log")).write_text(log)
    reports = re.findall(r"'" + namespace +
        r"\.(\w+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)", log, re.S)
    if sorted(n for n, _ in reports) != sorted(names):
        raise RuntimeError("Missing axiom reports")
    observed = {v.strip() for _, values in reports for v in values.split(",") if v.strip()}
    if observed - ALLOWED:
        raise RuntimeError("Unexpected axioms: " + repr(observed - ALLOWED))
    receipt = {"status": "PASS", "compiler": version.strip(), "declarations": len(names),
               "main_theorem": namespace + "." + manifest["main_theorem"],
               "axioms": sorted(observed), "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
               "qualification": "Compilation only; independent review and paper required before counting."}
    (build / "audit.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
