"""Validate only the I183 partial checkpoint integration scope."""
import ast
import json
import re
import runpy
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
REPO = ROOT.parent
BASE = "frontier/experiments/i183_cptp_survival/resumed"
ARCHIVE = "frontier/iterations/iteration183-cptp-finalization-factory-astra-task.json"
RECEIPT = "frontier/experiments/i183-parent-checkpoint-integration.json"
LEDGERS = ["README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"]
PARENT = [
    "frontier/experiments/i183-parent-checkpoint.py",
    "frontier/experiments/i183-parent-checkpoint-replay.json",
    "frontier/experiments/i183-parent-checkpoint-replay.stdout",
    "frontier/experiments/i183-parent-checkpoint-replay.stderr",
    "frontier/experiments/i183-parent-checkpoint-integrate.py",
    "frontier/iterations/i183-checkpoint-parent-disposition.md",
    "frontier/iterations/iteration183-cptp-finalization-brief.md",
]


def git(*args):
    return subprocess.check_output(["git", "-C", str(REPO), *args], text=True)


def main():
    preflight = sys.argv[1:] == ["--preflight"]
    assert preflight or not sys.argv[1:]
    assert not (ROOT / RECEIPT).exists()
    check = runpy.run_path(str(ROOT / PARENT[0]))
    before = check["authenticate"]()
    assert set(before["historically_drifted_context"]) == set(LEDGERS)
    inv = json.loads((ROOT / BASE / "checkpoint-inventory.json").read_bytes())
    owned = {x["path"] for x in inv["owned"]}
    scope = owned | set(inv["controls"]) | set(PARENT + LEDGERS + [ARCHIVE, RECEIPT])
    initial = json.loads((ROOT / PARENT[1]).read_bytes())
    assert initial["status"] == "PASS_PARTIAL_CHECKPOINT"
    assert not initial["sealed"] and not initial["full_mandatory_replay"]
    assert not git("diff", "--cached", "--name-only").strip()
    assert set(git("diff", "--name-only").splitlines()) == {
        "openai-proof-research/" + p for p in LEDGERS}
    python_count = json_count = links = 0
    empty, warnings = [], []
    for name in sorted(scope - {RECEIPT}):
        p = ROOT / name
        if preflight and name == ARCHIVE and not p.exists():
            continue
        data = p.read_bytes()
        if not data:
            assert p.suffix in (".stdout", ".stderr"), name
            empty.append(name)
        elif p.suffix == ".py":
            ast.parse(data, filename=name)
            python_count += 1
        elif p.suffix == ".json":
            json.loads(data)
            json_count += 1
        if p.suffix == ".md":
            for target in re.findall(r"\]\(([^)\s]+)\)", data.decode()):
                if "://" in target or target.startswith(("#", "mailto:")):
                    continue
                dest = (p.parent / target.split("#", 1)[0]).resolve()
                assert dest.exists() or (preflight and dest == ROOT / ARCHIVE), (name, target)
                links += 1
        whitespace = subprocess.run(
            ["git", "-C", str(REPO), "diff", "--no-index", "--check", "--", "/dev/null", str(p)],
            capture_output=True, text=True)
        assert not whitespace.stderr and whitespace.returncode in (0, 1, 2, 3)
        if whitespace.returncode & 2:
            assert name in owned and whitespace.stdout
            warnings.append({"path": name, "output": whitespace.stdout,
                             "reason": "Preserved authenticated checkpoint bytes"})
        else:
            assert not whitespace.stdout
    subprocess.run(["git", "-C", str(REPO), "diff", "--check"], check=True)
    replay = subprocess.run(
        [sys.executable, "-I", "-B", str(ROOT / BASE / "verify_checkpoint.py")],
        cwd=ROOT, capture_output=True, timeout=120)
    assert replay.returncode == 0 and not replay.stderr, replay.stderr
    result = json.loads(replay.stdout)
    assert result["status"] == "PASS_INCOMPLETE_CHECKPOINT_ONLY"
    assert result["mandatory_stage_prefix_recomputed"] == 12
    assert not result["full_mandatory_replay"] and not result["sealed"]
    assert result["forgery_positive_control"]
    assert len(result["eight_live_probes"]) == 8
    assert all(p["status"] == "BLOCKED" for p in result["eight_live_probes"])
    assert before == check["authenticate"]()
    assert json.loads(json.dumps(check["formal_certificates"]())) == \
        initial["independent_formal_certificates"]
    receipt = {
        "status": "PASS_PARTIAL_CHECKPOINT_INTEGRATION",
        "scope": ["openai-proof-research/" + p for p in sorted(scope)],
        "scope_count": len(scope), "python_parsed": python_count,
        "json_parsed": json_count, "local_links_checked": links,
        "preserved_empty_artifacts": empty, "retained_whitespace_warnings": warnings,
        "post_ledger_replay": result, "post_ledger_stderr": "empty",
        "all_four_contexts_changed_since_freeze": True,
        "current_context_stable": True, "strict_and_owned_bytes": "unchanged",
        "sealed": False, "full_mandatory_replay": False,
        "clean_clone_reconstruction": "not tested",
    }
    if not preflight:
        with (ROOT / RECEIPT).open("x") as f:
            json.dump(receipt, f, indent=2, sort_keys=True)
            f.write("\n")
    print(json.dumps({k: v for k, v in receipt.items()
                      if k not in ("scope", "post_ledger_replay")}, indent=2))
    print("Post-ledger partial replay:", result["total_seconds"], "seconds")


if __name__ == "__main__":
    main()
