#!/usr/bin/env python3
"""Check exact archive paths,unchanged seals and actual correctness dispatch."""
import datetime
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

OUT = Path(__file__).resolve().parent
BASE = OUT.parent
PROJECT = BASE.parents[2]
spec = importlib.util.spec_from_file_location('archive_helpers', OUT / 'replay.py')
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
sha, snap = helper.sha, helper.snap


def git(*args):
    return subprocess.check_output(['git', *args], cwd=PROJECT)


def check(mode):
    baseline = json.loads((OUT / 'integration-baseline.json').read_text())
    prefix = git('rev-parse', '--show-prefix').decode().strip()
    assert prefix == 'openai-proof-research/'
    head = baseline['head']
    if mode != 'committed':
        assert git('rev-parse', 'HEAD').decode().strip() == head
    taskpath = str((BASE / 'tasks.json').relative_to(PROJECT))
    old = json.loads(git('show', head + ':' + prefix + taskpath))
    new = json.loads((BASE / 'tasks.json').read_text())
    assert len(old['tasks']) == 475 and len(new['tasks']) == 476
    assert [i for i in range(475) if old['tasks'][i] != new['tasks'][i]] == [472]
    assert {k for k in old if old[k] != new[k]} == {'tasks', 'last_parent_progress', 'current_work_snapshot'}
    assert new['newAccepted'] == 19 and new['remaining'] == 1 and new['target'] == 20
    assert new['latestAcceptance'] == old['latestAcceptance'] == 'R041'
    s0, s = old['current_work_snapshot'], new['current_work_snapshot']
    assert {k for k in s0 if s0[k] != s[k]} == {
        'observed_utc', 'note', 'status_note', 'fresh_discovery_current',
        't3_current_confirmed_running', 't3_dispatch_observations', 't177c143_reviews'}
    assert set(s) - set(s0) == {'arithmetic_r107_archive'}
    assert s['t3_dispatch_observations'][:-1] == s0['t3_dispatch_observations']
    assert s['t3_last_polled_running'] == []
    assert new['tasks'][472]['status'] == 'completed' and new['tasks'][472]['nominee'] is None
    assert new['tasks'][475]['status'] == 'running' and new['tasks'][475]['review_gate'] == 'full_correctness'
    assert s['t3_current_confirmed_running'] == [new['tasks'][i]['taskId'] for i in [473, 474, 475]]
    assert s['fresh_discovery_current'] == ['fresh-analytic-discovery-r137']
    assert sha(BASE / new['tasks'][475]['brief']) == new['tasks'][475]['brief_sha256'] == 'd2ed3ab0fb02bb50a8b9c963f918becc4380220b98023759cab759ee0c75b0d1'
    review_before = s0['t177c143_reviews']
    review_now = s['t177c143_reviews']
    assert {k for k in review_before if review_before[k] != review_now[k]} == {'proof', 'proof_status'}
    assert set(review_now) - set(review_before) == {'proof_dispatch_record'}
    assert review_now['proof'] == new['tasks'][475]['taskId']
    assert review_now['proof_status'] == 'R1_RUNNING_AT_ACTUAL_DISPATCH'
    journal = PROJECT / 'frontier/NEW-TEN-2026-10-14.md'
    assert journal.read_bytes().startswith(git('show', head + ':' + prefix + 'frontier/NEW-TEN-2026-10-14.md'))
    root = BASE / 'fresh-arithmetic-discovery-r107'
    assert snap(root) == json.loads((OUT / 'observed-root.json').read_text())['root']
    replay = json.loads((OUT / 'replay.json').read_text())
    assert replay['original_order_defect_reproduced'] and replay['scratch_exclusion_demonstrated']
    for e in replay['late_named_originals']:
        if not e['mutable_observation']:
            assert sha(PROJECT / e['original']) == e['sha256']
    assert all(sha(PROJECT / p) == h for p, h in baseline['protected_unrelated_sha256'].items())
    author = BASE / 'fresh-structural-discovery-r143/packet/public'
    assert sha(author / 'frozen-scope.md') == 'cc916afef1373c1b3c0abdee271a4c2769f887f664e8c9b2b16b1b381c0de221'
    assert sha(author / 'author-proof.md') == '10e6dda7b9824e629922e3cf6f42de1b2bc194803ace97eb774c7dd85858792a'
    parent = BASE / 'discovery-structural-r143-parent'
    for n in ['assessment.md', 'intake.json', 'replay.py', 'replay.json', 'review-dispatch.json', 'proof-r1-brief.txt', 'contribution-r1-brief.txt']:
        rel = str((parent / n).relative_to(PROJECT))
        assert (parent / n).read_bytes() == git('show', head + ':' + prefix + rel)
    files = json.loads((OUT / 'staging-allowlist.json').read_text())['files']
    expected = {prefix + p for p in files}
    protected = {prefix + p for p in baseline['protected_unrelated_sha256']}
    if mode == 'prestage':
        assert not git('diff', '--cached', '--name-only')
        assert set(git('diff', '--name-only').decode().splitlines()) == protected | {
            prefix + taskpath, prefix + 'frontier/NEW-TEN-2026-10-14.md'}
        (OUT / 'integration-validation.json').write_text(json.dumps({
            'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'baseline_head': head, 'prestage_index_empty': True,
            'changed_existing_task_indices': [472], 'new_task_indices': [475],
            'other_tasks_and_unrelated_snapshot_fields_unchanged': True,
            'journal_prefix_and_actual_artifact_root_unchanged': True,
            'sealed_payload_and_original_defect_preserved': True,
            'exact_derived_correction_and_declared_scope_checked': True,
            'stable_named_originals_and_protected_unrelated_files_unchanged': True,
            'T177_scope_proof_both_briefs_and_historical_parent_records_unchanged': True,
            'full_correctness_actually_dispatched': True, 'contribution_status_or_body_not_polled': True,
            'explicit_allowed_paths': len(files), 'newAccepted': 19, 'remaining': 1,
            'publication': 'STOPPED', 'independent_mathematical_or_contribution_gate_assigned': False,
        }, indent=2) + '\n')
    else:
        if mode == 'staged':
            actual = set(git('diff', '--cached', '--name-only').decode().splitlines())
            obj = ':'
            subprocess.run(['git', 'diff', '--cached', '--check'], cwd=PROJECT, check=True)
        else:
            assert not git('diff', '--cached', '--name-only')
            assert git('rev-parse', 'HEAD^').decode().strip() == head
            actual = set(git('diff-tree', '--no-commit-id', '--name-only', '-r', 'HEAD').decode().splitlines())
            obj = 'HEAD:'
        assert actual == expected, (actual - expected, expected - actual)
        assert all(git('show', obj + prefix + p) == (PROJECT / p).read_bytes() for p in files)
        assert set(git('diff', '--name-only').decode().splitlines()) == protected
    print(json.dumps({'phase': mode, 'files': len(files), 'tasks': len(new['tasks']),
                      'count': 19, 'remaining': 1, 'sealed_roots_stable_inputs_and_T177_briefs_unchanged': True}))


if __name__ == '__main__':
    check(sys.argv[1])
