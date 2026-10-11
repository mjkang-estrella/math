"""Validate the exact I173 integration scope without touching unrelated work."""
import ast
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
REPO = ROOT.parent
BASE = ROOT / "frontier/experiments/i173_brace_high_loss_octagons"
RECEIPT = ROOT / "frontier/experiments/i173-parent-integration.json"
LEDGERS = ["README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"]
PARENT = [
    "frontier/experiments/i173-parent-validate.py",
    "frontier/experiments/i173-parent-certificates.py",
    "frontier/experiments/i173-parent-integrate.py",
    "frontier/experiments/i173-parent-precheck.json",
    "frontier/experiments/i173-parent-replay-stdout.json",
    "frontier/experiments/i173-parent-replay-stderr.txt",
    "frontier/experiments/i173-parent-verification.json",
    "frontier/experiments/i173-parent-certificates.json",
    "frontier/iterations/i173-brace-high-loss-octagons-parent-disposition.md",
    "frontier/iterations/iteration174-prism-gadget-survival-brief.md",
    "frontier/iterations/iteration174-prism-gadget-survival-factory-astra-task.json",
]


def git(*args):
    return subprocess.check_output(["git", "-C", str(REPO), *args], text=True)


def main():
    assert not RECEIPT.exists(), "Retain previous receipts"
    inv = json.loads((BASE / "inventory.json").read_bytes())
    paths = {ROOT / z["path"] for z in inv["owned"]}
    paths |= {BASE / n for n in ("inventory.json", "seal.json", "prevalidation.json")}
    paths |= {ROOT / name for name in PARENT + LEDGERS}
    for z in inv["owned"] + inv["external"]:
        raw = (ROOT / z["path"]).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == z["sha256"] and len(raw) == z["size"]
    controls = {BASE / n for n in ("inventory.json", "seal.json", "prevalidation.json")}
    actual = {ROOT / "frontier/iterations/i173-brace-high-loss-octagons.md"}
    for folder in (BASE, ROOT / "frontier/sources/i173_brace_high_loss_octagons"):
        actual |= {p for p in folder.rglob("*") if p.is_file()}
    assert actual - controls == {ROOT / z["path"] for z in inv["owned"]}
    seal = json.loads((BASE / "seal.json").read_bytes())
    for field, name in [("inventory_sha256", "inventory.json"),
                        ("prevalidation_sha256", "prevalidation.json")]:
        assert hashlib.sha256((BASE / name).read_bytes()).hexdigest() == seal[field]
    assert hashlib.sha256((BASE / "seal.json").read_bytes()).hexdigest() == (
        "6b824bffc72019f3c75dee02c70c1f0173b557cffc4275177f35bcb76356e609")
    for name in ("verification", "certificates"):
        assert json.loads((BASE.parent / ("i173-parent-"+name+".json")).read_text())["status"] == "PASS"
    assert not git("diff", "--cached", "--name-only").strip()
    assert set(git("diff", "--name-only").splitlines()) == {"openai-proof-research/"+p for p in LEDGERS}
    py = js = links = 0
    empty = []
    for p in sorted(paths):
        raw = p.read_bytes()
        if not raw:
            assert (p.parent == BASE and (p.name.endswith("-error.txt") or p.name == "audit_refinements-attempt-01.json")) or p.name == "i173-parent-replay-stderr.txt"
            empty.append(str(p.relative_to(ROOT)))
        elif p.name.endswith((".py", ".py.disabled")):
            ast.parse(raw, filename=str(p))
            py += 1
        elif p.name.endswith(".json"):
            json.loads(raw)
            js += 1
        if p.suffix == ".md":
            for target in re.findall(r"\]\(([^)\s]+)\)", raw.decode()):
                if "://" in target or target.startswith(("mailto:", "#")):
                    continue
                assert (p.parent / target.split("#", 1)[0]).exists(), (str(p), target)
                links += 1
    subprocess.run(["git", "-C", str(REPO), "diff", "--check"], check=True)
    scope = sorted(str(p.relative_to(REPO)) for p in paths | {RECEIPT})
    result = dict(status="PASS", scope=scope, scope_count=len(scope),
                  python_parsed=py, json_parsed=js, local_links_checked=links,
                  preserved_empty_artifacts=empty, sealed_non_context_bindings="unchanged",
                  outside_untracked_work="Not staged, modified, or deleted",
                  clean_clone_reconstruction="not performed")
    with RECEIPT.open("x") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({k: v for k, v in result.items() if k != "scope"}, indent=2))


if __name__ == "__main__":
    main()
