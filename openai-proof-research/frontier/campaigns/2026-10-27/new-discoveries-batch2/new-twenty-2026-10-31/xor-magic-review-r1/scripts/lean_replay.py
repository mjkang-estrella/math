#!/usr/bin/env python3
"""Independent fresh extraction and strict replay of xor-magic-r2-partial-source.zip.
Does not run the packet's replay.py or tools.  Every lean / leanchecker call is
run separately through scripts/capped.py (2 CPUs, 120 s CPU, 140 s wall, 6 GiB).
Usage: lean_replay.py [--stage build|check|controls|all]   (resumable; skips done steps)"""
import hashlib, json, os, re, subprocess, sys, zipfile, datetime, pathlib
ROOT = pathlib.Path(__file__).resolve().parent.parent
BASE = ROOT.parent
ZIP = BASE / "xor-magic-formal-r2" / "xor-magic-r2-partial-source.zip"
ZIP_SHA = "559d10bbe80307dc18b91fd857d21b00262c6f8b39acaa9aa671d28ecb919200"
LEANBIN = pathlib.Path("/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin")
PKGS = pathlib.Path("/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages")
EX = ROOT / "work" / "replay-r2"
STATE = ROOT / "receipts" / "lean-replay-state.json"

def sha(p): return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()

def extract():
    assert sha(ZIP) == ZIP_SHA, "zip hash mismatch"
    assert not EX.exists(), "extraction directory must be new"
    EX.mkdir(parents=True)
    z = zipfile.ZipFile(ZIP); members = []
    for i in z.infolist():
        n = i.filename; mode = i.external_attr >> 16
        assert not n.startswith("/") and ".." not in pathlib.PurePosixPath(n).parts and "\\" not in n, n
        assert (mode & 0o170000) == 0o100000, f"non-regular member {n}"
        assert not n.endswith((".olean", ".ilean", ".c")) and ".olean" not in n, n
        dest = EX / n; dest.parent.mkdir(parents=True, exist_ok=True)
        data = z.read(i); dest.write_bytes(data); os.chmod(dest, 0o644)
        members.append({"name": n, "size": len(data), "sha256": hashlib.sha256(data).hexdigest()})
    # compare extracted Lean sources with the lane's formal/ copies
    ident = {}
    for p in sorted((EX / "formal").glob("*.lean")):
        q = BASE / "xor-magic-formal-r2" / "formal" / p.name
        ident[p.name] = (q.exists() and sha(p) == sha(q))
    # forbidden-token scan over every extracted Lean file (comments included, conservative)
    pat = re.compile(r"\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern|opaque|partial|decide\s*\+\s*native|Lean\.ofReduceBool|ofReduceBool|reduceBool|macro|elab|syntax|initialize|builtin_initialize)\b")
    scan = {}
    for p in sorted(EX.rglob("*.lean")):
        hits = [(k + 1, l.strip()) for k, l in enumerate(p.read_text().splitlines()) if pat.search(l)]
        if hits: scan[str(p.relative_to(EX))] = hits
    for f in ("ReviewAudit.lean", "ReviewControls.lean", "ReviewBadEndpoint.lean", "ReviewBadCorrected.lean"):
        (EX / "review").mkdir(exist_ok=True)
        (EX / "review" / f).write_bytes((ROOT / "lean" / f).read_bytes())
    return {"zip": str(ZIP), "zip_sha256": sha(ZIP), "members": members, "formal_identical_to_lane": ident,
            "all_identical": all(ident.values()), "token_scan_hits": scan,
            "pre_existing_oleans": [str(p) for p in EX.rglob("*.olean*")]}

def topo():
    mods = {p.stem: p for p in (EX / "formal").glob("*.lean")}
    deps = {}
    for m, p in mods.items():
        deps[m] = [l.split()[1] for l in p.read_text().splitlines() if l.startswith("import ") and l.split()[1] in mods]
    order, seen = [], set()
    def visit(m, stack=()):
        assert m not in stack, "import cycle"
        if m in seen: return
        for d in deps[m]: visit(d, stack + (m,))
        seen.add(m); order.append(m)
    for m in sorted(mods): visit(m)
    return order

def env_cmd():
    lp = [str(EX / "formal")] + [str(x / ".lake/build/lib/lean") for x in sorted(PKGS.iterdir()) if x.is_dir()]
    (EX / "home").mkdir(exist_ok=True); (EX / "tmp").mkdir(exist_ok=True)
    return ["env", "-i", f"PATH={LEANBIN}:/usr/bin:/bin", f"HOME={EX/'home'}", f"TMPDIR={EX/'tmp'}",
            "MALLOC_ARENA_MAX=2", "LANG=C.UTF-8", "LEAN_PATH=" + ":".join(lp)]

def capped(name, cmd):
    r = subprocess.run([sys.executable, "-I", str(ROOT / "scripts" / "capped.py"), name, "--cwd", str(EX), "--"] + cmd,
                       capture_output=True, text=True)
    rec = json.loads((ROOT / "receipts" / f"run-{name}.json").read_text())
    return rec

def main():
    stage = sys.argv[sys.argv.index("--stage") + 1] if "--stage" in sys.argv else "all"
    st = json.loads(STATE.read_text()) if STATE.exists() else {}
    if "extraction" not in st:
        st["extraction"] = extract(); st["started_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        st["toolchain"] = subprocess.check_output([str(LEANBIN / "lean"), "--version"], text=True).strip()
        assert "4.34.1" in st["toolchain"] and "5045d0056413266e57c625dcd7c365b10e377c52" in st["toolchain"], st["toolchain"]
        st["order"] = topo()
        st["packet_modules_json"] = json.loads((EX / "modules.json").read_text())
        st["builds"] = {}; st["checks"] = {}; st["controls"] = {}
        STATE.write_text(json.dumps(st, indent=1))
    E = env_cmd(); lean = str(LEANBIN / "lean")
    if stage in ("build", "all"):
        for m in st["order"]:
            if st["builds"].get(m, {}).get("returncode") == 0: continue
            rec = capped(f"build-{m}", E + [lean, "-j1", "-DwarningAsError=true", "-o", f"formal/{m}.olean", f"formal/{m}.lean"])
            st["builds"][m] = rec; STATE.write_text(json.dumps(st, indent=1))
            print("BUILD", m, rec["returncode"], rec["wall_seconds"], rec["sampled_private_rss_peak_bytes"], flush=True)
            if rec["returncode"] != 0: sys.exit("build failed: " + m)
    if stage in ("check", "all"):
        for m in st["order"]:
            if st["checks"].get(m, {}).get("returncode") == 0: continue
            rec = capped(f"leanchecker-{m}", E + [str(LEANBIN / "leanchecker"), m])
            st["checks"][m] = rec; STATE.write_text(json.dumps(st, indent=1))
            print("CHECK", m, rec["returncode"], rec["wall_seconds"], flush=True)
            if rec["returncode"] != 0: sys.exit("leanchecker failed: " + m)
    if stage in ("controls", "all"):
        jobs = [("review-audit", ["review/ReviewAudit.lean"], True), ("review-controls", ["review/ReviewControls.lean"], True),
                ("review-bad-endpoint", ["review/ReviewBadEndpoint.lean"], False),
                ("review-bad-corrected", ["review/ReviewBadCorrected.lean"], False)]
        jobs += [(f"packet-neg-{p.stem}", [f"negative/{p.name}"], False) for p in sorted((EX / "negative").glob("*.lean"))]
        for name, args, expect_ok in jobs:
            if name in st["controls"] and st["controls"][name].get("as_expected"): continue
            rec = capped(name, E + [lean, "-j1", "-DwarningAsError=true"] + [str(EX / a) for a in args])
            log = (ROOT / "logs" / f"{name}.log").read_text()
            rec["expected_success"] = expect_ok
            rec["as_expected"] = (rec["returncode"] == 0) == expect_ok and rec["killed_reason"] is None
            if not expect_ok: rec["error_excerpt"] = log[:600]
            st["controls"][name] = rec; STATE.write_text(json.dumps(st, indent=1))
            print("CONTROL", name, rec["returncode"], "as_expected", rec["as_expected"], flush=True)
    st["finished_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    STATE.write_text(json.dumps(st, indent=1))

if __name__ == "__main__":
    main()
