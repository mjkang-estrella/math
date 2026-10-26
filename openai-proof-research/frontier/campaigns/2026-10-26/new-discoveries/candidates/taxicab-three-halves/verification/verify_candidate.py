#!/usr/bin/env python3
"""Replay every declaration of a candidate in isolation against pinned Lean/mathlib.

This verifies formal certificates only. It never changes discovery acceptance.
"""
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
    proc = subprocess.run(list(map(str, command)), text=True, capture_output=True, **kwargs)
    if proc.returncode:
        raise RuntimeError(proc.stdout + proc.stderr)
    return proc.stdout + proc.stderr


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("--lean-bin", type=Path, default=os.environ.get("LEAN_BIN",
        "/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean"))
    parser.add_argument("--packages", type=Path, default=os.environ.get("MATHLIB_PACKAGES",
        str(ROOT.parent.parent / "2026-10-14/formal/.lake/packages")))
    args = parser.parse_args()
    candidate = args.candidate.resolve()
    manifest = json.loads((candidate / "candidate.json").read_text())
    pins = json.loads((ROOT / "pins.json").read_text())
    build = candidate / "build/verified"
    build.mkdir(parents=True, exist_ok=True)
    receipt = build / "audit.json"
    receipt.unlink(missing_ok=True)
    version = run([args.lean_bin, "--version"]).strip()
    if f'version {pins["lean_version"]},' not in version:
        raise RuntimeError("Compiler version mismatch: " + version)
    packages = args.packages.resolve()
    deps = {"mathlib": pins["mathlib_revision"], **pins["dependencies"]}
    for name, expected in deps.items():
        if run(["git", "-C", packages / name, "rev-parse", "HEAD"]).strip() != expected:
            raise RuntimeError("Dependency revision mismatch: " + name)
        if run(["git", "-C", packages / name, "status", "--porcelain", "--untracked-files=no"]).strip():
            raise RuntimeError("Modified dependency: " + name)
    inventory = []
    sources = []
    modules = []
    for item in manifest["modules"]:
        module, namespace = item["module"], item["namespace"]
        if not re.fullmatch(r"[A-Za-z_]\w*", module) or not re.fullmatch(r"[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*", namespace):
            raise RuntimeError("Invalid module/namespace")
        path = candidate / "formal" / (module + ".lean")
        source = path.read_text()
        if re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", source):
            raise RuntimeError("Forbidden proof token: " + module)
        names = re.findall(r"^(?:noncomputable )?(?:abbrev|def|theorem|lemma)\s+(\w+)", source, re.M)
        if not names or len(names) != len(set(names)):
            raise RuntimeError("Invalid declaration inventory: " + module)
        inventory.extend(namespace + "." + name for name in names)
        (build / (module + ".lean")).write_bytes(path.read_bytes())
        (build / (module + ".olean")).unlink(missing_ok=True)
        modules.append(module)
        sources.append({"path": str(path.relative_to(candidate)),
                        "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                        "declarations": len(names)})
    if len(inventory) != len(set(inventory)) or not set(manifest["main_theorems"]) <= set(inventory):
        raise RuntimeError("Missing or duplicate main declarations")
    checks = "\n".join("import " + name for name in modules) + "\n\n"
    checks += "\n".join(f"#check {name}\n#print axioms {name}" for name in inventory) + "\n"
    (build / "Checks.lean").write_text(checks)
    (build / "Checks.olean").unlink(missing_ok=True)
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str,
        [build] + [packages / name / ".lake/build/lib/lean" for name in deps])))
    for module in modules + ["Checks"]:
        log = run([args.lean_bin, "-DwarningAsError=true", "-o", build / (module + ".olean"),
                   build / (module + ".lean")], cwd=build, env=env)
        (build / (module + ".log")).write_text(log)
    reports = re.findall(r"'([\w.]+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)", log, re.S)
    if sorted(name for name, _ in reports) != sorted(inventory):
        raise RuntimeError("Axiom inventory mismatch")
    observed = {value.strip() for _, values in reports for value in values.split(",") if value.strip()}
    if observed - ALLOWED:
        raise RuntimeError("Unexpected axioms: " + repr(observed - ALLOWED))
    result = {"status": "PASS", "compiler": version, "modules": sources,
              "declarations": len(inventory), "inventory": inventory,
              "main_theorems": manifest["main_theorems"], "axioms": sorted(observed),
              "qualification": "Formal replay only. Mathematical/source/novelty review and paper are separate gates."}
    receipt.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: result[key] for key in ["status", "declarations", "main_theorems", "axioms"]}, indent=2))


if __name__ == "__main__":
    main()
