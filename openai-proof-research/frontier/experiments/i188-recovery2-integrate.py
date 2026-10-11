"""I188 second provider-failure recovery integration and post-ledger replay.

No I188 mathematical output exists to validate. This script authenticates
the inherited I187/I183 chain, verifies that both failed runs left the
exclusive write scope empty, cross-checks the second-resume dispatch
archive against the first-resume and original dispatch archives, and
replays the sealed reference.
"""
import ast
import json
import runpy
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
REPO = ROOT.parent
ORIGINAL = "frontier/iterations/iteration188-patch-rooted-state-factory-astra-task.json"
RESUME = "frontier/iterations/iteration188-patch-rooted-state-factory-astra-resume-task.json"
RESUME2 = "frontier/iterations/iteration188-patch-rooted-state-codex-astra-resume2-task.json"
NOTE = "frontier/iterations/i188-provider-failure-recovery.md"
NOTE2 = "frontier/iterations/i188-provider-failure-recovery-2.md"
RECEIPT = "frontier/experiments/i188-recovery2-integration.json"
LEDGERS = ["README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"]
WRITE_SCOPE = [
    "frontier/iterations/i188-patch-rooted-state.md",
    "frontier/experiments/i188_patch_rooted_state/analytic-attempt.md",
    "frontier/experiments/i188_patch_rooted_state/reading-and-failures.md",
    "frontier/experiments/i188_patch_rooted_state/input-authentication.json",
    "frontier/sources/i188_patch_rooted_state/literature.md",
]
SELF = "frontier/experiments/i188-recovery2-integrate.py"


def git(*args):
    return subprocess.check_output(["git", "-C", str(REPO), *args], text=True)


def main():
    preflight = sys.argv[1:] == ["--preflight"]
    assert preflight or not sys.argv[1:]
    assert not (ROOT / RECEIPT).exists()
    validator = runpy.run_path(str(ROOT / "frontier/experiments/i187-parent-validate.py"))
    before = validator["authenticate"]()
    reference = validator["REFERENCE"]["authenticate"]()
    assert set(reference["context_drift"]) == set(LEDGERS)
    assert json.loads((ROOT /
        "frontier/experiments/i187-parent-verification.json").read_bytes())["status"] == "PASS"
    original = json.loads((ROOT / ORIGINAL).read_bytes())
    resume = json.loads((ROOT / RESUME).read_bytes())
    resume2 = json.loads((ROOT / RESUME2).read_bytes())
    # The failure chain: resume2's failed task is resume1, whose failed
    # task is the original dispatch; both failed with no outputs.
    failed2 = resume2["failed_task"]
    assert failed2["taskId"] == resume["taskId"]
    assert failed2["status"] == "failed" and failed2["output_files_written"] == 0
    failed1 = resume["failed_task"]
    assert failed1["taskId"] == original["dispatch_result"]["taskId"]
    assert failed1["status"] == "failed" and failed1["output_files_written"] == 0
    # Distinct clientRequestIds across all three attempts; identical
    # brief and write scope; provider driver changed only on resume2.
    ids = {original["clientRequestId"], resume["clientRequestId"],
           resume2["clientRequestId"]}
    assert len(ids) == 3
    assert resume2["write_scope"] == resume["write_scope"] == original["write_scope"] == WRITE_SCOPE
    assert resume2["continuation_brief"] == original["brief"]
    assert resume["continuation_brief"] == original["brief"]
    change = resume2["provider_change"]
    assert change["from"] == original["providerInstanceId"] == resume["providerInstanceId"]
    assert change["to"] == resume2["providerInstanceId"] != change["from"]
    assert resume2["model"] == original["model"] and change["model_family_unchanged"]
    # Both failed runs left the exclusive write scope empty (verified by
    # the parent after each failure, before this dispatch). Anything
    # present now must be the second resume's instructed incremental
    # writes, so every scoped file must postdate its dispatch.
    dispatch = 1760236539.362  # 2026-10-11T16:35:39.362Z, resume2 createdAt
    present = [name for name in WRITE_SCOPE if (ROOT / name).exists()]
    for name in present:
        assert (ROOT / name).stat().st_mtime > dispatch, name
    scope = set(LEDGERS + [ORIGINAL, RESUME, RESUME2, NOTE, NOTE2, SELF, RECEIPT])
    assert not git("diff", "--cached", "--name-only").strip()
    assert set(git("diff", "--name-only").splitlines()) == {
        "openai-proof-research/" + p for p in LEDGERS}
    py = js = links = 0
    for name in sorted(scope - {RECEIPT}):
        raw = (ROOT / name).read_bytes()
        assert raw, name
        if name.endswith(".py"):
            ast.parse(raw, filename=name)
            py += 1
        elif name.endswith(".json"):
            json.loads(raw)
            js += 1
        if name.endswith(".md"):
            import re
            for target in re.findall(r"\]\(([^)\s]+)\)", raw.decode()):
                if "://" in target or target.startswith(("#", "mailto:")):
                    continue
                dest = ((ROOT / name).parent / target.split("#", 1)[0]).resolve()
                assert dest.exists(), (name, target)
                links += 1
        check = subprocess.run(
            ["git", "-C", str(REPO), "diff", "--no-index", "--check", "--",
             "/dev/null", str(ROOT / name)],
            capture_output=True, text=True)
        assert check.returncode in (0, 1) and not check.stdout and not check.stderr, name
    subprocess.run(["git", "-C", str(REPO), "diff", "--check"], check=True)
    replay, proc = validator["replay"]()
    assert not proc.stderr
    assert before == validator["authenticate"]()
    assert reference == validator["REFERENCE"]["authenticate"]()
    receipt = {
        "status": "PASS", "scope": ["openai-proof-research/" + p for p in sorted(scope)],
        "scope_count": len(scope), "python_parsed": py, "json_parsed": js,
        "local_links_checked": links,
        "failed_runs_outputs_written": 0,
        "write_scope_verified_empty_after_each_failure": True,
        "write_scope_current_contents": (
            "only second-resume incremental writes, all postdating its dispatch"),
        "resume2_archive_consistent_with_prior_dispatches": True,
        "provider_driver_changed_model_family_unchanged": True,
        "post_ledger_replay": replay, "post_ledger_stderr": "empty",
        "all_four_contexts_historically_changed": True, "current_context_stable": True,
        "I187_output_bytes": "unchanged", "I183_sealed_bytes": "unchanged",
        "new_mathematical_acceptance": False, "I188_verdict": "none delivered",
        "local_ear_mechanism": "PARKED",
    }
    if not preflight:
        with (ROOT / RECEIPT).open("x") as out:
            json.dump(receipt, out, indent=2, sort_keys=True)
            out.write("\n")
    print(json.dumps({k: receipt[k] for k in (
        "status", "scope_count", "python_parsed", "json_parsed",
        "local_links_checked",
        "write_scope_verified_empty_after_each_failure")}))
    print("Inherited post-ledger replay:",
          replay["sealed_reference_replay"]["elapsed_seconds"], "seconds")


if __name__ == "__main__":
    main()
