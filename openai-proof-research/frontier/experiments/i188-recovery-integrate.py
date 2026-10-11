"""I188 provider-failure recovery integration and inherited post-ledger replay.

No I188 mathematical output exists to validate. This script authenticates
the inherited I187/I183 chain, verifies that the failed first run left the
exclusive write scope empty, cross-checks the resume dispatch archive
against the original dispatch archive, and replays the sealed reference.
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
NOTE = "frontier/iterations/i188-provider-failure-recovery.md"
RECEIPT = "frontier/experiments/i188-recovery-integration.json"
LEDGERS = ["README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"]
WRITE_SCOPE = [
    "frontier/iterations/i188-patch-rooted-state.md",
    "frontier/experiments/i188_patch_rooted_state/analytic-attempt.md",
    "frontier/experiments/i188_patch_rooted_state/reading-and-failures.md",
    "frontier/experiments/i188_patch_rooted_state/input-authentication.json",
    "frontier/sources/i188_patch_rooted_state/literature.md",
]
SELF = "frontier/experiments/i188-recovery-integrate.py"


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
    # The resume archive must point back at the failed original dispatch.
    failed = resume["failed_task"]
    assert failed["taskId"] == original["dispatch_result"]["taskId"]
    assert failed["status"] == "failed" and failed["output_files_written"] == 0
    assert resume["clientRequestId"] != original["clientRequestId"]
    assert resume["write_scope"] == original["write_scope"] == WRITE_SCOPE
    assert resume["continuation_brief"] == original["brief"]
    # The failed run left the exclusive write scope completely empty.
    for name in WRITE_SCOPE:
        assert not (ROOT / name).exists(), name
    assert not (ROOT / "frontier/experiments/i188_patch_rooted_state").exists()
    assert not (ROOT / "frontier/sources/i188_patch_rooted_state").exists()
    scope = set(LEDGERS + [ORIGINAL, RESUME, NOTE, SELF, RECEIPT])
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
        "failed_run_outputs_written": 0, "write_scope_verified_empty": True,
        "resume_archive_consistent_with_original_dispatch": True,
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
        "local_links_checked", "write_scope_verified_empty")}))
    print("Inherited post-ledger replay:",
          replay["sealed_reference_replay"]["elapsed_seconds"], "seconds")


if __name__ == "__main__":
    main()
