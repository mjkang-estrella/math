"""Exact finalization integration scope, with post-ledger sealed replay."""
import ast
import json
import re
import runpy
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
REPO = ROOT.parent
BASE = "frontier/experiments/i183_cptp_finalization"
ARCHIVE = "frontier/iterations/iteration184-alternating-cycle-factory-astra-task.json"
RECEIPT = "frontier/experiments/i183-final-parent-integration.json"
LEDGERS = ["README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"]
PARENT = ["frontier/experiments/i183-final-parent-" + p for p in
          ("validate.py", "replay.json", "replay.stdout", "replay.stderr",
           "certificates.py", "certificates.json", "integrate.py")]
PARENT += ["frontier/iterations/i183-finalization-parent-disposition.md",
           "frontier/iterations/iteration184-alternating-cycle-brief.md"]


def git(*args):
    return subprocess.check_output(["git", "-C", str(REPO), *args], text=True)


def main():
    preflight = sys.argv[1:] == ["--preflight"]
    assert preflight or not sys.argv[1:]
    assert not (ROOT / RECEIPT).exists()
    validator = runpy.run_path(str(ROOT / PARENT[0]))
    before = validator["authenticate"]()
    assert set(before["context_drift"]) == set(LEDGERS)
    inventory = json.loads((ROOT / BASE / "inventory.json").read_bytes())
    owned = {x["path"] for x in inventory["owned"]}
    scope = owned | set(inventory["controls"]) | set(PARENT + LEDGERS + [ARCHIVE, RECEIPT])
    for name in ("replay", "certificates"):
        assert json.loads((ROOT / ("frontier/experiments/i183-final-parent-" + name + ".json")
                           ).read_bytes())["status"] == "PASS"
    assert not git("diff", "--cached", "--name-only").strip()
    assert set(git("diff", "--name-only").splitlines()) == {
        "openai-proof-research/" + p for p in LEDGERS}
    py = js = links = 0
    empty, warnings = [], []
    for name in sorted(scope - {RECEIPT}):
        p = ROOT / name
        if preflight and name == ARCHIVE and not p.exists():
            continue
        raw = p.read_bytes()
        if not raw:
            assert p.suffix in (".stdout", ".stderr")
            empty.append(name)
        elif p.suffix == ".py":
            ast.parse(raw, filename=name)
            py += 1
        elif p.suffix == ".json":
            json.loads(raw)
            js += 1
        if p.suffix == ".md":
            for target in re.findall(r"\]\(([^)\s]+)\)", raw.decode()):
                if "://" in target or target.startswith(("#", "mailto:")):
                    continue
                dest = (p.parent / target.split("#", 1)[0]).resolve()
                assert dest.exists() or (preflight and dest == ROOT / ARCHIVE), (name, target)
                links += 1
        check = subprocess.run(
            ["git", "-C", str(REPO), "diff", "--no-index", "--check", "--", "/dev/null", str(p)],
            capture_output=True, text=True)
        assert not check.stderr and check.returncode in (0, 1, 2, 3)
        if check.returncode & 2:
            assert name in owned and check.stdout
            warnings.append({"path": name, "output": check.stdout,
                             "reason": "Preserve sealed bytes"})
        else:
            assert not check.stdout
    subprocess.run(["git", "-C", str(REPO), "diff", "--check"], check=True)
    replay, proc = validator["replay"]()
    assert replay["status"] == "PASS" and before == validator["authenticate"]()
    receipt = {
        "status": "PASS", "scope": ["openai-proof-research/" + p for p in sorted(scope)],
        "scope_count": len(scope), "python_parsed": py, "json_parsed": js,
        "local_links_checked": links, "preserved_empty_artifacts": empty,
        "retained_whitespace_warnings": warnings, "post_ledger_replay": replay,
        "post_ledger_stderr": "empty", "all_four_contexts_historically_changed": True,
        "current_context_stable": True, "sealed_bytes_and_strict_inputs": "unchanged",
        "new_mathematical_acceptance": False, "clean_clone_reconstruction": "not tested",
    }
    if not preflight:
        with (ROOT / RECEIPT).open("x") as out:
            json.dump(receipt, out, indent=2, sort_keys=True)
            out.write("\n")
    print(json.dumps({k: receipt[k] for k in (
        "status", "scope_count", "python_parsed", "json_parsed",
        "local_links_checked", "current_context_stable")}))
    print("Preserved empty captures:", len(empty), "; sealed whitespace warnings:", len(warnings))
    print("Post-ledger 23-stage replay:", replay["elapsed_seconds"], "seconds")


if __name__ == "__main__":
    main()
