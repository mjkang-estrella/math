"""Exact I175 integration scope, preflight and preserved evidence checks."""
import ast
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
REPO = ROOT.parent
BASE = ROOT / "frontier/experiments/i175_affected_prism_exterior"
RECEIPT = BASE.parent / "i175-parent-integration.json"
ARCHIVE = ROOT / "frontier/iterations/iteration176-uniform-five-port-rank-factory-astra-task.json"
LEDGERS = ["README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"]
PARENT = [
    "frontier/experiments/i175-parent-validate.py",
    "frontier/experiments/i175-parent-certificates.py",
    "frontier/experiments/i175-parent-integrate.py",
    "frontier/experiments/i175-parent-precheck.json",
    "frontier/experiments/i175-parent-replay-stdout.json",
    "frontier/experiments/i175-parent-replay-stderr.txt",
    "frontier/experiments/i175-parent-verification.json",
    "frontier/experiments/i175-parent-certificates.json",
    "frontier/iterations/i175-affected-prism-exterior-parent-disposition.md",
    "frontier/iterations/iteration176-uniform-five-port-rank-brief.md",
]


def git(*args):
    return subprocess.check_output(["git", "-C", str(REPO), *args], text=True)


def main():
    preflight = sys.argv[1:] == ["--preflight"]
    assert preflight or not sys.argv[1:]
    assert not RECEIPT.exists()
    inv = json.loads((BASE / "inventory.json").read_bytes())
    owned = {ROOT / z["path"] for z in inv["owned"]}
    controls = {BASE / n for n in ("inventory.json", "prevalidation.json", "seal.json")}
    actual = {ROOT / "frontier/iterations/i175-affected-prism-exterior.md"}
    for d in (BASE, ROOT / "frontier/sources/i175_affected_prism_exterior"):
        actual |= {p for p in d.rglob("*") if p.is_file()}
    assert actual - controls == owned
    paths = owned | controls | {ROOT / n for n in PARENT + LEDGERS} | {ARCHIVE}
    for z in inv["owned"] + inv["external"]:
        raw = (ROOT / z["path"]).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == z["sha256"] and len(raw) == z["size"]
    assert hashlib.sha256((BASE / "seal.json").read_bytes()).hexdigest() == (
        "42636ad1d8a669c8bee23332d7059e0ba957c3467a343ea2b563fdf346905c31")
    seal = json.loads((BASE / "seal.json").read_bytes())
    for name in ("inventory", "prevalidation"):
        assert hashlib.sha256((BASE / (name+".json")).read_bytes()).hexdigest() == seal[name+"_sha256"]
    for name in ("verification", "certificates"):
        assert json.loads((BASE.parent / ("i175-parent-"+name+".json")).read_bytes())["status"] == "PASS"
    assert not git("diff", "--cached", "--name-only").strip()
    assert set(git("diff", "--name-only").splitlines()) == {"openai-proof-research/"+n for n in LEDGERS}
    py = js = links = 0
    empty, warnings = [], []
    for p in sorted(paths):
        if preflight and p == ARCHIVE and not p.exists():
            continue
        raw = p.read_bytes()
        if not raw:
            assert (p.parent == BASE and (p.name.endswith("-stderr.txt") or p.name in {
                "mandatory-attempt-01.json", "historical-attempt-01.json"})) or p.name == "i175-parent-replay-stderr.txt"
            empty.append(str(p.relative_to(ROOT)))
        elif p.name.endswith((".py", ".py.disabled")):
            ast.parse(raw, filename=str(p))
            py += 1
        elif p.suffix == ".json":
            json.loads(raw)
            js += 1
        if p.suffix == ".md":
            for target in re.findall(r"\]\(([^)\s]+)\)", raw.decode()):
                if "://" in target or target.startswith(("mailto:", "#")):
                    continue
                dest = p.parent / target.split("#", 1)[0]
                assert dest.exists() or (preflight and dest == ARCHIVE), (p, target)
                links += 1
        check = subprocess.run(["git", "-C", str(REPO), "diff", "--no-index", "--check",
                                "--", "/dev/null", str(p)], capture_output=True, text=True)
        assert not check.stderr and check.returncode in (0, 1, 2, 3), (p, check)
        if check.returncode & 2:
            assert p in owned and check.stdout, "Unexpected parent whitespace issue"
            warnings.append(dict(path=str(p.relative_to(ROOT)), output=check.stdout, preserved="sealed bytes"))
        else:
            assert not check.stdout
    subprocess.run(["git", "-C", str(REPO), "diff", "--check"], check=True)
    result = dict(status="PASS", scope=sorted(str(p.relative_to(REPO)) for p in paths | {RECEIPT}),
                  scope_count=len(paths)+1, python_parsed=py, json_parsed=js,
                  local_links_checked=links, preserved_empty_artifacts=empty,
                  retained_whitespace_warnings=warnings, non_context_bindings="unchanged",
                  replay_context_limit="I175 pins inventory-current ledger hashes; accepted parent replay predates integration edits.",
                  clean_clone_reconstruction="not tested")
    if not preflight:
        with RECEIPT.open("x") as out:
            json.dump(result, out, indent=2, sort_keys=True)
            out.write("\n")
    print(json.dumps({k: v for k, v in result.items() if k != "scope"}, indent=2))


if __name__ == "__main__":
    main()
