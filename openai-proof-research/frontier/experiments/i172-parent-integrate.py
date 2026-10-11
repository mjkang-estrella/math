"""Validate I172's exact integration scope; leave unrelated work untouched."""
import ast
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
REPO = ROOT.parent
BASE = ROOT / "frontier/experiments/i172_prescribed_square_switch"
RECEIPT = ROOT / "frontier/experiments/i172-parent-integration.json"
LEDGERS = ["README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"]
PARENT = [
    "frontier/experiments/i172-parent-validate.py",
    "frontier/experiments/i172-parent-certificates.py",
    "frontier/experiments/i172-parent-integrate.py",
    "frontier/experiments/i172-parent-precheck.json",
    "frontier/experiments/i172-parent-replay-stdout.json",
    "frontier/experiments/i172-parent-replay-stderr.txt",
    "frontier/experiments/i172-parent-verification.json",
    "frontier/experiments/i172-parent-certificates.json",
    "frontier/iterations/i172-prescribed-square-switch-parent-disposition.md",
    "frontier/iterations/iteration173-brace-high-loss-octagons-brief.md",
    "frontier/iterations/iteration173-brace-high-loss-octagons-factory-astra-task.json",
]


def git(*args):
    return subprocess.check_output(["git", "-C", str(REPO), *args], text=True)


def main():
    assert not RECEIPT.exists(), "Retain any previous receipt"
    inv = json.loads((BASE / "inventory.json").read_bytes())
    paths = {ROOT / z["path"] for z in inv["owned"]}
    paths |= {BASE / n for n in ("inventory.json", "seal.json", "prevalidation.json")}
    paths |= {ROOT / name for name in PARENT + LEDGERS}
    for z in inv["owned"] + inv["external"]:
        if z.get("role") != "context-only":
            raw = (ROOT / z["path"]).read_bytes()
            assert hashlib.sha256(raw).hexdigest() == z["sha256"] and len(raw) == z["size"]
    seal = json.loads((BASE / "seal.json").read_bytes())
    for field, name in [("inventory_sha256", "inventory.json"),
                        ("prevalidation_sha256", "prevalidation.json")]:
        assert hashlib.sha256((BASE / name).read_bytes()).hexdigest() == seal[field]
    assert hashlib.sha256((BASE / "seal.json").read_bytes()).hexdigest() == (
        "8abdc63ae868fbbda7778e422da34194d918be99e15fc29b784cc6468140c972")
    for name in ("verification", "certificates"):
        assert json.loads((BASE.parent / ("i172-parent-"+name+".json")).read_text())["status"] == "PASS"
    assert not git("diff", "--cached", "--name-only").strip()
    assert set(git("diff", "--name-only").splitlines()) == {"openai-proof-research/"+p for p in LEDGERS}
    py = js = links = 0
    empty = []
    for p in sorted(paths):
        raw = p.read_bytes()
        if not raw:
            assert p.parent == BASE and (p.name.endswith("-error.txt") or p.name == "authenticate-attempt-01.json")
            empty.append(str(p.relative_to(ROOT)))
        elif p.name.endswith((".py", ".py.disabled")):
            ast.parse(raw, filename=str(p))
            py += 1
        elif p.name.endswith((".json", ".json.disabled")):
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
    result = {"status": "PASS", "scope": scope, "scope_count": len(scope),
              "python_parsed": py, "json_parsed": js, "local_links_checked": links,
              "preserved_empty_artifacts": empty, "sealed_non_context_bindings": "unchanged",
              "outside_untracked_work": "Not staged, modified, or deleted",
              "clean_clone_reconstruction": "not performed"}
    with RECEIPT.open("x") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({k: v for k, v in result.items() if k != "scope"}, indent=2))


if __name__ == "__main__":
    main()
