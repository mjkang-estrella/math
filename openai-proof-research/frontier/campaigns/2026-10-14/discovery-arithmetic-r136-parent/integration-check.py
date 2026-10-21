#!/usr/bin/env python3
"""Bounded checks for immutable T054L136 intake and two first review launches."""
import datetime, importlib.util, json, stat, subprocess, sys
from pathlib import Path

O = Path(__file__).resolve().parent
B = O.parent
P = B.parents[2]
spec = importlib.util.spec_from_file_location('replay', O / 'replay.py')
h = importlib.util.module_from_spec(spec)
spec.loader.exec_module(h)

def read(path):
    return json.loads(path.read_text())

def git(*args):
    return subprocess.check_output(['git', *args], cwd=P)

def main(mode):
    base = read(O / 'integration-baseline.json')
    head = base['head']
    prefix = git('rev-parse', '--show-prefix').decode().strip()
    assert prefix == 'openai-proof-research/'
    if mode != 'committed':
        assert git('rev-parse', 'HEAD').decode().strip() == head
    path = str((B / 'tasks.json').relative_to(P))
    old = json.loads(git('show', head + ':' + prefix + path))
    new = read(B / 'tasks.json')
    assert len(old['tasks']) == 575 and len(new['tasks']) == 577
    assert [i for i in range(575) if old['tasks'][i] != new['tasks'][i]] == [571, 573]
    assert {k for k in old if old[k] != new[k]} == {'tasks', 'last_parent_progress', 'current_work_snapshot'}
    assert new['newAccepted'] == 19 and new['remaining'] == 1 and new['target'] == 20
    assert new['latestAcceptance'] == old['latestAcceptance'] == 'R041'
    previous, current = old['current_work_snapshot'], new['current_work_snapshot']
    assert {k for k in previous if previous[k] != current[k]} == {
        'observed_utc', 'note', 'status_note', 't3_current_confirmed_running',
        'fresh_discovery_current', 't3_dispatch_observations', 'pending_terminal_intakes_20261021'}
    assert set(current) - set(previous) == {
        'arithmetic_r136_intake', 'arithmetic_r136_reviews', 'arithmetic136_review_prospective_isolation'}
    assert not set(previous) - set(current)
    assert current['t3_dispatch_observations'][:-2] == previous['t3_dispatch_observations']
    assert not current['t3_last_polled_running']
    assert current['fresh_discovery_current'] == ['fresh-structural-discovery-r172']
    assert current['t3_current_confirmed_running'] == [new['tasks'][i]['taskId'] for i in [574, 575, 576]]
    intake = read(O / 'intake.json')
    assert current['arithmetic_r136_intake'] == intake
    assert current['pending_terminal_intakes_20261021'] == [intake['analytic_r164_terminal_pending_parent_archive']]
    for index, name in [(571, 'task-status.json'), (573, 'analytic-r164-notified-terminal.json'),
                        (575, 'proof-r1-dispatch.json'), (576, 'contribution-r1-dispatch.json')]:
        raw = read(O / name)['structuredContent']
        assert all(new['tasks'][index][k] == v for k, v in raw.items())
    nominee = new['tasks'][571]
    assert nominee['parent_disposition'] == 'FULL_AUTHOR_PROOF_NOMINEE_PENDING_INDEPENDENT_REVIEWS'
    assert nominee['scope_frozen'] and nominee['nominee'] == 'T054L136'
    assert nominee['correctness'] == nominee['contribution'] == 'UNREVIEWED'
    assert new['tasks'][573]['parent_disposition'] == 'TERMINAL_RESULT_PENDING_PARENT_INTAKE'
    assert h.sha(O / 'assessment.md') == intake['assessment_sha256']
    assert h.sha(O / 'preflight.md') == intake['preflight_sha256']
    receipt = read(O / 'prospective-isolation.json')
    prep = read(O / 'review-preparation.json')
    assert receipt['before_both_review_briefs_and_roots']
    assert receipt['both_original_initial_active_peer_briefs_exclude_entire_arithmetic136_namespace']
    assert receipt['mutual_review_exclusions_prepared_before_any_review_dispatch']
    assert receipt['no_active_peer_body_read_poll_or_steer']
    assert receipt['review_preparation'] == prep
    assert prep['both_empty_exclusive_roots_created_before_either_dispatch'] and prep['same_original_P1_before_both_dispatches']
    assert prep['assessment_sha256'] == intake['assessment_sha256']
    assert prep['preflight_sha256'] == intake['preflight_sha256']
    for peer in receipt['existing_active_peer_original_initial_briefs']:
        task = old['tasks'][peer['task_index']]
        assert peer['taskId'] == task['taskId'] and peer['brief'] == task['brief']
        assert h.sha(B / peer['brief']) == peer['sha256'] == task['brief_sha256']
        assert peer['literal_existing_exclusion'].encode() in (B / peer['brief']).read_bytes()
    root = B / 'fresh-arithmetic-discovery-r136'
    frozen, proof = root / 'FROZEN.md', root / 'notes/author-proof.md'
    assert h.sha(frozen) == prep['frozen_sha256'] == intake['frozen_scope_sha256'] == h.FROZEN
    assert h.sha(proof) == prep['author_proof_sha256'] == intake['author_proof_sha256'] == h.PROOF
    for index, rec in zip([575, 576], prep['records']):
        task = new['tasks'][index]
        assert task['providerInstanceId'] == 'codex' and task['model'] == 'gpt-6-astra'
        assert {x['id']: x['value'] for x in task['options']} == {'reasoningEffort': 'high', 'serviceTier': 'default'}
        assert task['status'] == 'running' and not task['hasPendingChildRuns'] and not task['hasPendingQuestion'] and task['pendingApproval'] is None
        assert task['output'] == rec['root'] and task['brief'] == rec['brief']
        assert h.sha(B / task['brief']) == rec['brief_sha256'] == task['brief_sha256']
        text = (B / task['brief']).read_text()
        assert text.split('--- ENTIRE UNCHANGED FROZEN STATEMENT ---\n')[1] == frozen.read_text()
        assert (O / 'preflight.md').read_text() in text
        assert all(x in text for x in ['*structural*r172*', '*analytic*r164*', '*arithmetic*r137*'])
        assert ('*arithmetic*r136*contribution*' if index == 575 else '*arithmetic*r136*proof*') in text
        assert not task['accepted'] and task['count_change'] == 0
    assert current['t3_dispatch_observations'][-2:] == [read(O / n) for n in ['proof-r1-dispatch.json', 'contribution-r1-dispatch.json']]
    observed = read(O / 'observed-root.json')
    assert h.snap(root) == observed['root'] and stat.S_IMODE(root.stat().st_mode) == observed['root_mode']
    assert all(h.sha(P / e['path']) == e['sha256'] for e in read(O / 'replay.json')['stable_named_originals'])
    previous_parent = B / 'discovery-analytic-r161-parent'
    for name, parent in [('fresh-analytic-discovery-r161', previous_parent),
                         ('analytic-r161-proof-r1', previous_parent / 'proof-r1-adoption'),
                         ('analytic-r161-contribution-r1', previous_parent / 'contribution-r1-adoption')]:
        assert h.snap(B / name) == read(parent / 'observed-root.json')['root']
    assert all(h.sha(P / path) == value for path, value in base['protected_unrelated_sha256'].items())
    journal_path = 'frontier/NEW-TEN-2026-10-14.md'
    old_journal = git('show', head + ':' + prefix + journal_path)
    assert len(old_journal) == base['journal_bytes']
    assert (P / journal_path).read_bytes().startswith(old_journal)
    files = read(O / 'staging-allowlist.json')['files']
    assert len(files) == len(set(files)) == 30
    assert len([x for x in files if '/fresh-arithmetic-discovery-r136/' in x]) == 11
    assert not any('/private/' in x or '/controls/' in x or '/arithmetic-r136-proof-r1/' in x
                   or '/arithmetic-r136-contribution-r1/' in x or '/fresh-analytic-discovery-r164/' in x
                   or '/fresh-structural-discovery-r172/' in x or x.endswith(('/observed-root.json', '/replay.json')) for x in files)
    expected = {prefix + x for x in files}
    protected = {prefix + x for x in base['protected_unrelated_sha256']}
    if mode == 'prestage':
        assert not git('diff', '--cached', '--name-only')
        assert set(git('diff', '--name-only').decode().splitlines()) == protected | {prefix + path, prefix + journal_path}
        result = {'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  'baseline_head': head, 'changed_existing_task_indices': [571, 573],
                  'new_review_task_indices': [575, 576], 'other_tasks_and_snapshot_fields_unchanged': True,
                  'entire_frozen_scope_and_proof_hashes_unchanged': True,
                  'same_open_parent_P1_and_mutual_guards_prepared_before_either_dispatch': True,
                  'actual_model_and_options_checked': True, 'analytic164_terminal_pending_separate_archive': True,
                  'sealed_author_and_closed_analytic161_roots_unchanged': True,
                  'protected_identity_replay_metadata_local_unstaged': True,
                  'journal_prefix_and_protected_unrelated_files_unchanged': True,
                  'explicit_allowed_paths': 30, 'newAccepted': 19, 'remaining': 1,
                  'publication': 'STOPPED', 'mathematical_gate_assigned': False}
        (O / 'integration-validation.json').write_text(json.dumps(result, indent=2) + '\n')
    else:
        if mode == 'staged':
            actual = set(git('diff', '--cached', '--name-only').decode().splitlines())
            obj = ':'
            subprocess.run(['git', 'diff', '--cached', '--check'], cwd=P, check=True)
        else:
            assert mode == 'committed' and not git('diff', '--cached', '--name-only')
            assert git('rev-parse', 'HEAD^').decode().strip() == head
            actual = set(git('diff-tree', '--no-commit-id', '--name-only', '-r', 'HEAD').decode().splitlines())
            obj = 'HEAD:'
        assert actual == expected, (actual - expected, expected - actual)
        assert all(git('show', obj + prefix + x) == (P / x).read_bytes() for x in files)
        assert set(git('diff', '--name-only').decode().splitlines()) == protected
    print(json.dumps({'phase': mode, 'files': 30, 'tasks': 577, 'count': 19, 'remaining': 1, 'sealed_roots_unchanged': True}))

if __name__ == '__main__':
    main(sys.argv[1])
