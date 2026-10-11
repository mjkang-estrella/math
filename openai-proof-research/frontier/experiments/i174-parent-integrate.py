"""Scope, syntax, links and retained-whitespace checks before integration."""
import ast
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
REPO = ROOT.parent
BASE = ROOT / "frontier/experiments/i174_prism_gadget_survival"
RECEIPT = BASE.parent / "i174-parent-integration.json"
ARCHIVE = ROOT / "frontier/iterations/iteration175-affected-prism-exterior-factory-astra-task.json"
LEDGERS = ["README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"]
PARENT = [
    "frontier/experiments/i174-parent-validate.py",
    "frontier/experiments/i174-parent-certificates.py",
    "frontier/experiments/i174-parent-integrate.py",
    "frontier/experiments/i174-parent-precheck.json",
    "frontier/experiments/i174-parent-replay-stdout.json",
    "frontier/experiments/i174-parent-replay-stderr.txt",
    "frontier/experiments/i174-parent-verification.json",
    "frontier/experiments/i174-parent-certificates.json",
    "frontier/iterations/i174-prism-gadget-survival-parent-disposition.md",
    "frontier/iterations/iteration175-affected-prism-exterior-brief.md",
]


def git(*args):
    return subprocess.check_output(["git", "-C", str(REPO), *args], text=True)


def main():
    preflight = sys.argv[1:] == ["--preflight"]
    assert preflight or not sys.argv[1:]
    assert not RECEIPT.exists()
    inv = json.loads((BASE / "inventory.json").read_bytes())
    paths = {ROOT / z["path"] for z in inv["owned"]}
    controls = {BASE / n for n in ("inventory.json", "prevalidation.json", "seal.json")}
    actual = {ROOT / "frontier/iterations/i174-prism-gadget-survival.md"}
    for d in (BASE, ROOT / "frontier/sources/i174_prism_gadget_survival"):
        actual |= {p for p in d.rglob("*") if p.is_file()}
    assert actual - controls == paths
    paths |= controls | {ROOT / n for n in PARENT + LEDGERS} | {ARCHIVE}
    for z in inv["owned"] + inv["external"]:
        raw = (ROOT / z["path"]).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == z["sha256"] and len(raw) == z["size"]
    assert hashlib.sha256((BASE / "seal.json").read_bytes()).hexdigest() == (
        "b63e358e0506567a2098d61dfe164a2f2b4db721488105d16dd238cdc06886ef")
    seal = json.loads((BASE / "seal.json").read_bytes())
    for name in ("inventory", "prevalidation"):
        assert hashlib.sha256((BASE / (name+".json")).read_bytes()).hexdigest() == seal[name+"_sha256"]
    for name in ("verification", "certificates"):
        assert json.loads((BASE.parent / ("i174-parent-"+name+".json")).read_bytes())["status"] == "PASS"
    assert not git("diff", "--cached", "--name-only").strip()
    assert set(git("diff", "--name-only").splitlines()) == {"openai-proof-research/"+n for n in LEDGERS}
    py = js = links = 0
    empty, warnings = [], []
    for p in sorted(paths):
        if preflight and p == ARCHIVE and not p.exists():
            continue
        raw = p.read_bytes()
        if not raw:
            assert (p.parent == BASE and p.name.endswith(("-error.txt", "-stdout.txt"))) or p.name == "i174-parent-replay-stderr.txt"
            empty.append(str(p.relative_to(ROOT)))
        elif p.name.endswith((".py", ".py.disabled")):
            ast.parse(raw, filename=str(p))
            py += 1
        elif p.suffix == ".json":
            json.loads(raw)
            js += 1
        if p.suffix == ".md":
            # Bound historical snapshots retain their original relative-link base.
            parent = ROOT / "frontier/iterations" if p.name in {
                "parent-disposition-initial.md", "parent-disposition-reviewed-current.md",
                "build-failure-01-report.md"} else p.parent
            for target in re.findall(r"\]\(([^)\s]+)\)", raw.decode()):
                if "://" in target or target.startswith(("mailto:", "#")):
                    continue
                destination = parent / target.split("#", 1)[0]
                assert destination.exists() or (preflight and destination == ARCHIVE), (p, target)
                links += 1
        check = subprocess.run(["git", "-C", str(REPO), "diff", "--no-index", "--check",
                                "--", "/dev/null", str(p)], capture_output=True, text=True)
        # --no-index sets the ordinary difference bit even for clean new files.
        assert not check.stderr and check.returncode in (0, 1, 2, 3), (p, check)
        if check.returncode & 2:
            assert check.stdout
            assert p in {ROOT / z["path"] for z in inv["owned"]}, "New parent whitespace issue"
            warnings.append(dict(path=str(p.relative_to(ROOT)), output=check.stdout, preserved="sealed bytes"))
        else:
            assert not check.stdout
    subprocess.run(["git", "-C", str(REPO), "diff", "--check"], check=True)
    scope = sorted(str(p.relative_to(REPO)) for p in paths | {RECEIPT})
    result = dict(status="PASS", scope=scope, scope_count=len(scope), python_parsed=py,
                  json_parsed=js, local_links_checked=links, preserved_empty_artifacts=empty,
                  retained_whitespace_warnings=warnings,
                  snapshot_link_policy="Historical snapshots resolve relative links in frontier/iterations",
                  non_context_bindings="unchanged", clean_clone_reconstruction="not tested")
    if not preflight:
        with RECEIPT.open("x") as out:
            json.dump(result, out, indent=2, sort_keys=True)
            out.write("\n")
    print(json.dumps({k: v for k, v in result.items() if k != "scope"}, indent=2))


if __name__ == "__main__":
    main()
