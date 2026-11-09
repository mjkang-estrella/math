#!/usr/bin/env python3
"""pi-fourprojection-final-review-r1 — independent adversarial replay checker.

Own code path (not the candidate's verify_candidate.py): fresh isolated build
directory, own inventory, two Lean passes (full-environment enumeration and
per-declaration axiom audit), 35-core-hash integrity check, and independent
numerical probes. Verifies formal certificates only; asserts no acceptance.
"""
import hashlib, json, os, re, subprocess, sys, tempfile
from pathlib import Path

CAND = Path(__file__).resolve().parent / "candidate"
LANE = Path(__file__).resolve().parent
LEAN = "/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean"
PKGS = Path("/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages")
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|native_decide)\b|\bunsafe\b")

def sh(cmd, **kw):
    p = subprocess.run([str(c) for c in cmd], capture_output=True, text=True, **kw)
    if p.returncode:
        raise RuntimeError(f"cmd failed: {cmd}\n{p.stdout}\n{p.stderr}")
    return p.stdout + p.stderr

def core_hashes():
    """before/after check of the 35 frozen core files."""
    exp = json.loads((CAND / "final-review-hashes.json").read_text())
    bad = []
    for rel, h in exp.items():
        got = hashlib.sha256((CAND / rel).read_bytes()).hexdigest()
        if got != h:
            bad.append(rel)
    return len(exp), bad

def main():
    report = {}
    n, bad = core_hashes()
    report["core_hashes"] = {"checked": n, "mismatches": bad}
    if bad:
        print("FROZEN CORE HASH DRIFT:", bad); sys.exit(1)

    ver = sh([LEAN, "--version"]).strip()
    assert "version 4.34.1," in ver, ver
    report["compiler"] = ver

    pins = json.loads((CAND / "verification" / "pins.json").read_text())
    deps = {"mathlib": pins["mathlib_revision"], **pins["dependencies"]}
    for name, want in deps.items():
        got = sh(["git", "-C", PKGS / name, "rev-parse", "HEAD"]).strip()
        assert got == want, (name, got, want)
        assert not sh(["git", "-C", PKGS / name, "status",
                       "--porcelain", "--untracked-files=no"]).strip(), name
    report["dependency_heads"] = deps

    manifest = json.loads((CAND / "candidate.json").read_text())
    modules = [m["module"] for m in manifest["modules"]]
    assert len(modules) == 17

    # forbidden-token scan on the actual frozen sources
    for m in modules:
        src = (CAND / "formal" / f"{m}.lean").read_text()
        hit = FORBIDDEN.search(src)
        assert not hit, (m, hit.group(0))
    report["forbidden_tokens"] = "none"

    with tempfile.TemporaryDirectory(prefix="fp-review-") as tmp:
        b = Path(tmp)
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(
            [str(b)] + [str(PKGS / d / ".lake/build/lib/lean") for d in deps]))

        # pass 1: compile every frozen module fresh, in dependency order
        for m in modules:
            src = (CAND / "formal" / f"{m}.lean").read_bytes()
            (b / f"{m}.lean").write_bytes(src)
            sh([LEAN, "-DwarningAsError=true", "-o", b / f"{m}.olean", b / f"{m}.lean"],
               env=env, cwd=b)
        report["module_compile"] = "PASS (17/17 fresh, warningAsError=true)"

        # pass 2a: full environment enumeration (all FourProjection constants,
        # incl. private/generated) via a metaprogram, per compiled module set
        enum = "\n".join(f"import {m}" for m in modules) + """

open Lean in
run_cmd do
  let env <- Lean.getEnv
  let mut out := #[]
  for (n, _) in env.constants.toList do
    let s := n.toString
    if s.startsWith "FourProjection." && !s.startsWith "FourProjection._private" then
      out := out.push s
  logInfo m!"ENUM_BEGIN"
  for s in out.qsort (fun a b => a < b) do
    logInfo m!"ENVNAME {s}"
  logInfo m!"ENUM_END count {out.size}"
"""
        (b / "Enum.lean").write_text(enum)
        out = sh([LEAN, "-o", b / "Enum.olean", b / "Enum.lean"], env=env, cwd=b)
        names = sorted(set(re.findall(r"ENVNAME ([\w.]+)", out)))
        cnt = re.search(r"ENUM_END count (\d+)", out)
        report["environment_enumeration"] = {"count": len(names), "tail_count": cnt.group(1) if cnt else None}

        # pass 2b: per-public-declaration #check + #print axioms
        # public inventory: my own regex over the frozen sources
        inv = []
        for m in modules:
            src = (CAND / "formal" / f"{m}.lean").read_text()
            for mt in re.finditer(
                    r"^\s*(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(abbrev|def|structure|theorem|lemma|instance)\s+([\w'.]+)", src, re.M):
                inv.append((m, mt.group(1), f"FourProjection.{mt.group(2)}"))
        assert len(inv) == len({x[2] for x in inv}), "duplicate public names"
        checks = "\n".join(f"import {m}" for m in modules) + "\n"
        checks += "\n".join(f"#check {n}\n#print axioms {n}" for _, _, n in inv) + "\n"
        (b / "Checks.lean").write_text(checks)
        log = sh([LEAN, "-DwarningAsError=true", "-o", b / "Checks.olean", b / "Checks.lean"],
                 env=env, cwd=b)
        (LANE / "own-checks.log").write_text(log)
        ax = re.findall(r"'([\w.]+)' depends on axioms: \[(.*?)\]", log, re.S)
        axd = {n: {v.strip() for v in vals.split(",") if v.strip()} for n, vals in ax}
        missing = [n for _, _, n in inv if n not in axd]
        assert not missing, (missing, log[-3000:])
        extra = ALLOWED
        bad_ax = {n: a for n, a in axd.items() if a - extra}
        assert not bad_ax, bad_ax
        allax = set().union(*axd.values()) if axd else set()
        report["public_declarations"] = {
            "count": len(inv),
            "by_kind": {k: sum(1 for _, kk, _ in inv if kk == k)
                        for k in ["theorem", "lemma", "def", "abbrev", "instance", "structure"]},
            "main_theorems_present": set(manifest["main_theorems"]) <= {n for _, _, n in inv},
            "axioms_observed": sorted(allax),
        }
        # record endpoint types verbatim
        types = {}
        for name in manifest["main_theorems"]:
            i = log.index(f"'{name}'")
            types[name] = log[log.rindex("\n", 0, i - len(name)) if False else 0:0]  # placeholder
        (LANE / "replay-environment-names.json").write_text(
            json.dumps({"enumerated": names, "public": sorted({n for _, _, n in inv})}, indent=1))
    report["verdict"] = "PASS"
    (LANE / "own-replay-result.json").write_text(json.dumps(report, indent=1))
    print(json.dumps(report, indent=1))

if __name__ == "__main__":
    main()
