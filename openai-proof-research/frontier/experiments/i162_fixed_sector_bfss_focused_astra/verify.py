"""Offline, read-only verification. No ancestor code is imported or executed."""
import sys
sys.dont_write_bytecode = True
import os
import hashlib
import json
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
SREL = "frontier/sources/i162_fixed_sector_bfss_focused_astra"
EREL = "frontier/experiments/i162_fixed_sector_bfss_focused_astra"
RREL = "frontier/reviews/i162-fixed-sector-bfss-focused-astra.md"
SOURCE = ROOT / SREL
ALLOWED_ARGS = ([], ["--prevalidate"])


def require(condition, detail):
    if not condition:
        raise RuntimeError(detail)


def deny_effects(event, args):
    if event == "open":
        path, mode, flags = args
        forbidden_flags = os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND
        if (isinstance(mode, str) and any(c in mode for c in "wax+")) or flags & forbidden_flags:
            raise PermissionError("read-only verifier: file write denied")
        if isinstance(path, (str, bytes)) and os.fsdecode(path).endswith((".pyc", ".pyo")):
            raise PermissionError("verifier: bytecode file access denied")
    forbidden = (
        "socket.", "subprocess.", "pty.", "os.exec", "os.spawn", "os.posix_spawn",
        "os.fork", "os.system", "os.remove", "os.rename", "os.rmdir", "os.mkdir",
        "os.chmod", "os.chown", "os.truncate", "os.utime", "os.link", "os.symlink",
        "os.chdir", "shutil.", "ctypes.",
    )
    if event.startswith(forbidden):
        raise PermissionError("read-only verifier: denied " + event)


sys.addaudithook(deny_effects)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def load(rel):
    return json.loads((ROOT / rel).read_bytes())


def safe_path(rel):
    require(isinstance(rel, str) and not Path(rel).is_absolute(), "relative inventory path required")
    require(".." not in Path(rel).parts, "path traversal")
    p = ROOT / rel
    require(not p.is_symlink() and p.resolve().is_relative_to(ROOT), "symlink or out-of-root input")
    return p


def item(rel):
    p = safe_path(rel)
    data = p.read_bytes()
    return {"path": rel, "bytes": len(data), "sha256": sha(data)}


def inventory():
    paths = [RREL]
    for directory in [SREL, EREL]:
        for p in (ROOT / directory).rglob("*"):
            require(not p.is_symlink(), "owned symlink forbidden")
            if p.is_file() and p != SOURCE / "seal.json":
                paths.append(str(p.relative_to(ROOT)))
    return [item(p) for p in sorted(paths)]


def validate_rows(rows):
    require([x["path"] for x in rows] == sorted(set(x["path"] for x in rows)),
            "inventory not canonical or unique")
    for x in rows:
        require(item(x["path"]) == x, "immutable mismatch: " + x["path"])


def diagnostics(pinned, task_bindings):
    # This function is called only after every immutable and reading check below.
    texrel = next(x["local"]["path"] for x in pinned if x["upstream_path"].endswith(".tex"))
    tex = safe_path(texrel).read_text()
    original = safe_path("frontier/iterations/i155-fixed-sector-bfss-counting.md").read_text()
    require(r"B(x)=\tfrac i2" in tex, "source coefficient witness absent")
    require(r"=\tfrac i2 f_{abc}" in tex, "source proof coefficient witness absent")
    require("B(D_s)=2i sum_" in original, "original incorrect coefficient witness absent")
    metric_cases = 0
    for x in range(2, 15):
        for y in range(1, x):
            a, b = x*x+y*y, -2*x*y
            determinant = a*a-b*b
            require(determinant == (x*x-y*y)**2, "metric determinant")
            for left, right in [(1, 0), (0, 1), (1, 1), (1, -1), (2, -3)]:
                inverse = Fraction(a*(left*left+right*right)-2*b*left*right, determinant)
                diagonal = Fraction((left+right)**2, 2*(x-y)**2) + Fraction((left-right)**2, 2*(x+y)**2)
                require(inverse == diagonal, "angular metric inverse")
                metric_cases += 1
    require(Fraction(3072+9, 3)-1024 == 3 and 3080 > 3072+6, "sector threshold")
    require(384**2*6 < 1024**2 and 96**2*6 < 1024**2, "norm budget")
    require(Fraction(1, 3) * Fraction(1, 96) * Fraction(3, 4) * Fraction(64, 45)
            == Fraction(1, 270), "gamma/momentum rational prefactor")
    c, C = Fraction(3), Fraction(1024)
    eps = c / (2*(c+C))
    require((1-eps)*c-eps*C == c/2, "coercivity interpolation")
    # Test the guard itself without touching the filesystem/network/process table.
    blocked = 0
    for event, args in [
        ("open", ("never-created", "w", os.O_WRONLY | os.O_CREAT)),
        ("open", ("never-read.pyc", "r", os.O_RDONLY)),
        ("socket.__new__", ()), ("subprocess.Popen", ()),
        ("os.remove", ()), ("os.rename", ()), ("os.system", ()),
    ]:
        try:
            deny_effects(event, args)
        except PermissionError:
            blocked += 1
        else:
            raise RuntimeError("guard negative test did not deny " + event)
    return {
        "status": "PASS", "metric_quadratic_cases": metric_cases,
        "guard_negative_tests": blocked, "source_coefficient_ratio": 4,
        "original_exact_B_claim": "FAIL",
        "sector_constants_and_rational_phase_prefactor": "PASS",
        "scope": "Finite exact checks only; not domain proof, Weyl proof, contribution or acceptance",
    }


def main():
    require(sys.argv[1:] in ALLOWED_ARGS, "supported arguments: none or --prevalidate")
    pre = sys.argv[1:] == ["--prevalidate"]
    seal_path = SOURCE / "seal.json"
    if pre:
        require(not seal_path.exists(), "prevalidation prohibited after sealing")
        owned = inventory()
    else:
        require(seal_path.is_file(), "missing final seal")
        seal = json.loads(seal_path.read_bytes())
        require(seal["schema"] == "I162-focused-evidence-v1", "wrong seal schema")
        owned = seal["inventory"]
        validate_rows(owned)
        require(inventory() == owned, "owned inventory membership changed")
        require(sha(json.dumps(owned, sort_keys=True, separators=(",", ":")).encode())
                == seal["inventory_sha256"], "inventory digest mismatch")

    refs = load(SREL + "/references.json")
    validate_rows(refs)
    baseline = load(SREL + "/ancestor-baseline.json")
    validate_rows(baseline)
    require(not (ROOT / "frontier/sources/i158_fixed_sector_bfss_counting_r2/seal.json").exists(),
            "historical I158 seal status changed; do not silently reinterpret history")
    # Baseline directories must not lose or gain preparation artifacts unnoticed.
    for directory in [
        "frontier/sources/i158_fixed_sector_bfss_counting_r2",
        "frontier/experiments/i158_fixed_sector_bfss_counting_r2",
    ]:
        actual = sorted(str(p.relative_to(ROOT)) for p in (ROOT / directory).rglob("*") if p.is_file())
        expected = sorted(x["path"] for x in baseline if x["path"].startswith(directory + "/"))
        require(actual == expected, "ancestor inventory changed: " + directory)

    ledgers = load(SREL + "/live-ledgers.json")
    require({x["live_path"] for x in ledgers} ==
            {"README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md", "frontier/iterations/README.md"},
            "wrong live-ledger allowance")
    drift = []
    for x in ledgers:
        require(item(x["snapshot"]["path"]) == x["snapshot"], "snapshot mismatch")
        if sha(safe_path(x["live_path"]).read_bytes()) != x["snapshot"]["sha256"]:
            drift.append(x["live_path"])

    tree = load("sources/preprints-tree.json")
    require(tree["truncated"] is False, "truncated source tree forbidden")
    indexed = {x["path"]: x for x in tree["tree"]}
    pins = load(SREL + "/pinned-sources.json")
    for x in pins:
        require(item(x["local"]["path"]) == x["local"], "pinned source changed")
        b = safe_path(x["local"]["path"]).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(b)).encode() + b"\0" + b).hexdigest()
        require(blob == x["git_sha"] == indexed[x["upstream_path"]]["sha"], "pinned blob mismatch")
        require(x["upstream_commit"] == load("sources/upstream.json")["commit"], "pin mismatch")

    tasks = load(SREL + "/task-bindings.json")
    for x in tasks:
        d = load(x["path"])
        require(list(d) == x["keys_in_order"], "task field order")
        require(len(d["brief"]) == x["brief_characters"], "brief length")
        require(safe_path(x["brief_view"]).read_text() == d["brief"], "brief not lossless")
        require(load(x["other_fields_view"]) == {k: v for k, v in d.items() if k != "brief"},
                "other task fields not lossless")

    reads = load(SREL + "/read-manifest.json")
    for x in reads:
        b = safe_path(x["path"]).read_bytes()
        require(sha(b) == x["sha256"] and len(b) == x["bytes"], "read source mismatch")
        t = b.decode("utf-8")
        lines = t.split("\n")
        start = sum(len(y)+1 for y in lines[:x["line_first"]-1])
        end = sum(len(y)+1 for y in lines[:x["line_last"]]) if x["line_last"] < len(lines) else len(t)
        require((start, end) == (x["character_start"], x["character_end"]), "reading interval mismatch")
        passage = t[start:end]
        require(sha(passage.encode()) == x["range_sha256"] and passage[-180:] == x["ending"],
                "read passage mismatch")
        require(len(t) == x["characters_total"] and t.count("\n") == x["raw_lf"]
                and len(t.splitlines()) == x["python_splitlines"], "read length mismatch")

    # Complete coverage is required only for the exact focused prerequisites.
    required_full = [x["brief_view"] for x in tasks] + [x["other_fields_view"] for x in tasks]
    required_full += [
        "frontier/iterations/i155-fixed-sector-bfss-counting.md",
        "frontier/reviews/i158-fixed-sector-bfss-counting-r2.md",
        next(x["local"]["path"] for x in pins if x["upstream_path"].endswith(".tex")),
        "frontier/sources/i155_fixed_sector_bfss_counting/external/fnt.txt",
    ]
    for rel in required_full:
        cursor = 0
        for x in sorted((x for x in reads if x["path"] == rel), key=lambda x: x["character_start"]):
            require(x["character_start"] <= cursor, "semantic receipt gap: " + rel)
            cursor = max(cursor, x["character_end"])
        require(cursor == len(safe_path(rel).read_text()), "incomplete focused coverage: " + rel)
    scope = load(SREL + "/scope.json")
    require(scope["original_package_verdict"] == "FAIL", "original verdict silently changed")
    if pre:
        diagnostic_result = {"status": "NOT RUN before final seal"}
    else:
        diagnostic_result = diagnostics(pins, tasks)
    result = {
        "status": "PASS", "mode": "preseal-read-only" if pre else "sealed-offline-read-only",
        "original_package_verdict": scope["original_package_verdict"],
        "historical_i158_gate": scope["historical_i158_gate"],
        "all_immutable_checks_before_new_diagnostics": True,
        "canonical_owned_files": len(owned), "immutable_references": len(refs),
        "preserved_ancestor_files": len(baseline), "read_ranges": len(reads),
        "pinned_blobs_checked": len(pins), "live_ledger_drift": sorted(drift),
        "ancestor_executions": 0, "network_processes_writes_bytecode": "denied",
        "diagnostics": diagnostic_result,
        "scope": "Evidence integrity and finite checks only; not universal proof or acceptance",
    }
    if pre:
        result["prevalidated_inventory"] = owned
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
