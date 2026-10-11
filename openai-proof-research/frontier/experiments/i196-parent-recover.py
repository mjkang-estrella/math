"""Validate I196's parent recovery checkpoint, not a mathematical result.

The live child output paths are deliberately outside the integration scope.
Only the observed initial copies are frozen. No historical proof scripts run.
"""
import ast
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
REPO = ROOT.parent
CHECKPOINT = "frontier/experiments/i196_recovery_checkpoint"
MANIFEST = "frontier/experiments/i196-parent-recovery.json"
SCRIPT = "frontier/experiments/i196-parent-recover.py"
RECEIPT = "frontier/experiments/i196-parent-recovery-verification.json"
DISPOSITION = "frontier/iterations/i196-fresh-discovery-parent-checkpoint.md"
LEDGERS = {"README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"}
PARTIAL_HASHES = {
    "report.md": "8beb7526d15d030f26315b8f5addec3e64ec837e2e57977b7a357a91a19e1784",
    "analytic-attempt.md": "3b5960347fefa338066488c652609ccbe18d3a3fd85dfdaccccdb88dd29e20b4",
    "reading-and-failures.md": "00c336670210ce92b84b124fd017cde7ec4a46f3628c8906324772d1a5b0a351",
    "input-authentication.json": "5c4be735f78c7091ce5fbb4d753d317e61ade5d081512aeb7287aa89225891c7",
    "literature.md": "6d54688a9ee81e39981b9abe18adfbdb59d81697e61aca7053748c612e1574f1",
}
OVERLAP_INPUTS = {
    "frontier/iterations/i36-harmonic-analysis-discovery.md",
    "frontier/reviews/i36-common-geometric-avoidance-novelty-r3.md",
    "frontier/iterations/i37-supergeometric-avoidance.md",
    "frontier/iterations/i07-arithmetic.md",
    "frontier/iterations/i99-quantitative-arithmetic-patterns-discovery.md",
}
SCOPE = LEDGERS | {MANIFEST, SCRIPT, RECEIPT, DISPOSITION} | {
    f"{CHECKPOINT}/{name}" for name in PARTIAL_HASHES}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args):
    return subprocess.check_output(
        ["git", "-C", str(REPO), *args], text=True).splitlines()


def validate(preflight):
    record = json.loads((ROOT / MANIFEST).read_bytes())
    assert record["accepted_findings"] == 8
    assert record["remaining_findings"] == 2
    assert record["mathematical_verdict"].startswith("NOT REVIEWABLE")
    assert record["original_task"]["status"] == "cancelled"
    assert record["original_task"]["hasPendingChildRuns"] is True
    later, delivery = record["later_run"], record["correction_delivery"]
    assert later["ordinal"] == 2 and later["runId"].endswith(":ordinal:2")
    assert later["status_at_observation"] == "running"
    assert delivery["mode"] == "steer" and delivery["delivery"] == "steered"
    assert delivery["runId"] == later["runId"]
    assert delivery["taskId"] != record["original_task"]["taskId"]
    assert delivery["clientRequestId"] == "mathdb-i196-active-overlap-correction-20261011"
    assert len(record["partial_snapshots"]) == 5
    found = set()
    for path in (ROOT / CHECKPOINT).rglob("*"):
        assert not path.is_symlink(), path
        if path.is_file():
            found.add(path.relative_to(ROOT / CHECKPOINT).as_posix())
    assert found == set(PARTIAL_HASHES)
    snapshot_names = set()
    originals = set()
    for row in record["partial_snapshots"]:
        name = Path(row["snapshot"]).name
        assert row["snapshot"] == f"{CHECKPOINT}/{name}"
        assert name not in snapshot_names and row["original"] not in originals
        snapshot_names.add(name)
        originals.add(row["original"])
        path = ROOT / row["snapshot"]
        assert digest(path) == row["sha256"] == PARTIAL_HASHES[name]
        assert path.stat().st_size == row["size_bytes"]
        assert "PARTIAL" in path.read_text()
    assert snapshot_names == set(PARTIAL_HASHES)
    assert not SCOPE.intersection(originals), "Never stage live child outputs"
    auth = json.loads(
        (ROOT / CHECKPOINT / "input-authentication.json").read_bytes())
    assert len(auth["anchors"]) == 6 and len(auth["other_inputs"]) == 2
    assert auth["retrieved_sources"] == [] and auth["unsealed"] is True
    refs = record["input_hashes"]
    expected_refs = {row["path"] for row in auth["anchors"] + auth["other_inputs"]}
    expected_refs |= OVERLAP_INPUTS | {
        "frontier/iterations/iteration196-fresh-discovery-task.json"}
    assert set(refs) == expected_refs
    for row in auth["anchors"] + auth["other_inputs"]:
        assert refs[row["path"]] == row["sha256"]
    for name, expected in refs.items():
        assert not (ROOT / name).is_symlink()
        assert digest(ROOT / name) == expected, name
    assert not git("diff", "--cached", "--name-only"), "Unexpected staged work"
    changed = set(git("diff", "--name-only"))
    prefixed_scope = {"openai-proof-research/" + name for name in SCOPE}
    assert changed & prefixed_scope == {
        "openai-proof-research/" + name for name in LEDGERS}
    outside_scope = sorted(changed - prefixed_scope)
    assert len(SCOPE) == 13
    before = {name: digest(ROOT / name) for name in SCOPE - {RECEIPT}}
    links = 0
    for name in sorted(SCOPE - {RECEIPT}):
        path = ROOT / name
        assert not path.is_symlink()
        raw = path.read_bytes()
        if path.suffix == ".py":
            ast.parse(raw, filename=name)
        elif path.suffix == ".json":
            json.loads(raw)
        elif path.suffix == ".md":
            for target in re.findall(r"\]\(([^)\s]+)\)", raw.decode()):
                if "://" in target or target.startswith(("#", "mailto:")):
                    continue
                dest = (path.parent / target.split("#", 1)[0]).resolve()
                assert dest.exists() or dest == ROOT / RECEIPT, (name, target)
                links += 1
        check = subprocess.run(
            ["git", "-C", str(REPO), "diff", "--no-index", "--check",
             "--", "/dev/null", str(path)], capture_output=True, text=True)
        assert check.returncode in (0, 1)
        assert not check.stdout and not check.stderr, (name, check.stdout, check.stderr)
    subprocess.run(["git", "-C", str(REPO), "diff", "--check"], check=True)
    assert before == {name: digest(ROOT / name) for name in before}
    result = {
        "status": "PASS",
        "validation_scope": "Provenance and parent integration only",
        "scope": ["openai-proof-research/" + name for name in sorted(SCOPE)],
        "scope_count": len(SCOPE),
        "artifact_sha256": before,
        "snapshot_count": len(PARTIAL_HASHES),
        "immutable_input_count": len(refs),
        "local_links_checked": links,
        "live_child_outputs_excluded": True,
        "outside_scope_tracked_changes_excluded": outside_scope,
        "original_task_status": "cancelled",
        "later_run_status_at_observation": "running",
        "correction_delivery": "steered into ordinal 2",
        "mathematical_tests": "Not run: no I196 mathematical deduction exists in checkpoint",
        "new_mathematical_acceptance": False,
        "accepted_findings": 8,
        "remaining_findings": 2,
    }
    if not preflight:
        with (ROOT / RECEIPT).open("x") as out:
            json.dump(result, out, indent=2, sort_keys=True)
            out.write("\n")
    print(json.dumps({key: result[key] for key in (
        "status", "scope_count", "snapshot_count", "immutable_input_count",
        "local_links_checked", "live_child_outputs_excluded")}))


if __name__ == "__main__":
    assert sys.flags.isolated and sys.dont_write_bytecode
    assert sys.argv[1:] in ([], ["--preflight"])
    validate(sys.argv[1:] == ["--preflight"])
