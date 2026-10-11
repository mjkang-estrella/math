"""Validate the exact I171 integration manifest without staging any files."""
import ast
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
REPO = ROOT.parent
BASE = ROOT / "frontier/experiments/i171_square_switch_weight"
RECEIPT = ROOT / "frontier/experiments/i171-parent-integration.json"
LEDGERS = ["README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"]
PARENT = [
    "frontier/experiments/i171-parent-validate.py",
    "frontier/experiments/i171-parent-certificates.py",
    "frontier/experiments/i171-parent-integrate.py",
    "frontier/experiments/i171-parent-precheck.json",
    "frontier/experiments/i171-parent-replay-stdout.json",
    "frontier/experiments/i171-parent-replay-stderr.txt",
    "frontier/experiments/i171-parent-verification.json",
    "frontier/experiments/i171-parent-certificates.json",
    "frontier/iterations/i171-square-switch-weight-parent-disposition.md",
    "frontier/iterations/iteration172-prescribed-square-switch-brief.md",
    "frontier/iterations/iteration172-prescribed-square-switch-factory-astra-task.json",
]


def git(*args):
    return subprocess.check_output(["git", "-C", str(REPO), *args], text=True)


def main():
    assert not RECEIPT.exists(), "Preserve an earlier integration receipt"
    inv = json.loads((BASE / "inventory.json").read_bytes())
    controls = ["inventory.json", "seal.json", "prevalidation.json"]
    paths = {ROOT / z["path"] for z in inv["files"]}
    paths |= {BASE / name for name in controls}
    paths |= {ROOT / name for name in PARENT + LEDGERS}
    for z in inv["files"]:
        p = ROOT / z["path"]
        assert hashlib.sha256(p.read_bytes()).hexdigest() == z["sha256"]
    seal = json.loads((BASE / "seal.json").read_bytes())
    for field, name in [("inventory_sha256", "inventory.json"),
                        ("prevalidation_sha256", "prevalidation.json")]:
        assert hashlib.sha256((BASE / name).read_bytes()).hexdigest() == seal[field]
    assert hashlib.sha256((BASE / "seal.json").read_bytes()).hexdigest() == (
        "0cd340b50cfd23a041bdab7baf827e1d8c26e279e9a7705caecd49a7d2eefedf")
    assert json.loads((ROOT / "frontier/experiments/i171-parent-verification.json").read_text())["status"] == "PASS"
    assert json.loads((ROOT / "frontier/experiments/i171-parent-certificates.json").read_text())["status"] == "PASS"
    assert git("diff", "--cached", "--name-only").strip() == "", "Unrelated staged work"
    modified = set(git("diff", "--name-only").splitlines())
    assert modified == {"openai-proof-research/" + n for n in LEDGERS}, modified
    py = js = links = 0
    empty = []
    for p in sorted(paths):
        raw = p.read_bytes()
        if not raw:
            assert p.parent == BASE and (
                p.name.endswith("-error.txt") or
                p.name in {"audit-attempt-01.json", "coefficient-audit-attempt-01.json"}
            ), str(p)
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
                target = target.split("#", 1)[0]
                assert (p.parent / target).exists(), (str(p), target)
                links += 1
    subprocess.run(["git", "-C", str(REPO), "diff", "--check"], check=True)
    scope = sorted(str(p.relative_to(REPO)) for p in paths | {RECEIPT})
    receipt = {"status": "PASS", "scope": scope, "scope_count": len(scope),
               "python_parsed": py, "json_parsed": js, "local_links_checked": links,
               "preserved_empty_artifacts": empty, "owned_sealed_bytes": "unchanged",
               "outside_untracked_work": "Not staged, modified, or deleted",
               "clean_clone_reconstruction": "not performed"}
    with RECEIPT.open("x") as stream:
        json.dump(receipt, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({k: v for k, v in receipt.items() if k != "scope"}, indent=2))


if __name__ == "__main__":
    main()
