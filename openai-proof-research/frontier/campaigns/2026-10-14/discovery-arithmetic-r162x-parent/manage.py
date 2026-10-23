#!/usr/bin/env python3
"""One-shot committed-baseline CAS: archive r162x and register r162y."""
from pathlib import Path
from datetime import datetime, timezone
import copy
import fnmatch
import hashlib
import json
import re
import subprocess

P = Path(__file__).resolve().parents[4]
D = Path(__file__).resolve().parent
B = P / 'frontier/campaigns/2026-10-14'
N = B / 'discovery-arithmetic-r162y-parent'
T = 'frontier/campaigns/2026-10-14/tasks.json'
J = 'frontier/NEW-TEN-2026-10-14.md'
load = lambda path: json.loads(path.read_bytes())
sha = lambda raw: hashlib.sha256(raw).hexdigest()
git = lambda *args: subprocess.check_output(['git', *args], cwd=P)


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def main():
    assert not (D / 'integration-guard.json').exists(), 'already integrated; do not rerun'
    assert not git('diff', '--cached', '--name-only'), 'occupied index'
    baseline = load(D / 'intake-baseline.json')
    for path, expected in baseline['protected'].items():
        assert sha((P / path).read_bytes()) == expected
    head = git('rev-parse', 'HEAD').decode().strip()
    raw = {path: git('show', f'{head}:openai-proof-research/{path}') for path in (T, J)}
    for path, content in raw.items():
        assert (P / path).read_bytes() == content, 'uncommitted coordination; defer safely'
    before = json.loads(raw[T])
    initial = load(D / 'private/intake/tasks-before.json')
    assert before['tasks'][702] == initial['tasks'][702], 'own record advanced; reconcile first'
    assert (before['newAccepted'], before['target'], before['remaining'], before['latestAcceptance']) == (19, 20, 1, 'R041')
    assert len(before['tasks']) >= baseline['taskCount']
    paths = [str(D.relative_to(P)), str(N.relative_to(P)),
             'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162y',
             'frontier/campaigns/2026-10-14/expanded-target-2026-10-17/fresh-arithmetic-r162y-brief.txt']
    extra = []
    for index in range(baseline['taskCount'], len(before['tasks'])):
        task = before['tasks'][index]
        if task.get('status') not in ('running', 'queued', 'waiting', 'starting'):
            continue
        content = (P / task['brief']).read_bytes()
        patterns = [s for s in re.findall(r'\*[^\s,;()]*\*', content.decode()) if s not in ('*', '**')]
        matches = {path: [s for s in patterns if fnmatch.fnmatchcase(path.casefold(), s.casefold())] for path in paths}
        assert all(matches.values()), 'new original peer guard does not cover future writes'
        extra.append({'index': index, 'brief': task['brief'], 'sha256': sha(content), 'matches': matches})
    save(D / 'coordination-rebase.json', {'baseline_head': baseline['head'], 'head_before': head,
         'committed_rebase_needed': head != baseline['head'], 'new_original_brief_guard_checks': extra,
         'foreign_liveness_findings_or_bodies_not_queried': True})
    for path, content in raw.items():
        (D / 'private/intake' / ('tasks-integration-before.json' if path == T else 'journal-integration-before.md')).write_bytes(content)
    terminal = load(D / 'task-status.json')['structuredContent']
    assert terminal['taskId'] == before['tasks'][702]['taskId']
    assert terminal['status'] == 'completed' and terminal['workState'] == 'result_available'
    assert not terminal['hasPendingChildRuns'] and not terminal['hasPendingQuestion'] and not terminal['pendingApproval']
    intake = load(D / 'intake.json')
    assert intake['disposition'] == 'PREFREEZE_NO_NOMINEE_ARCHIVED'
    assert load(D / 'verification.json')['result'] == 'MATCH'
    dispatch = load(N / 'dispatch.json')['structuredContent']
    assert dispatch['providerInstanceId'] == 'codex' and dispatch['model'] == 'gpt-6-astra'
    assert dict((x['id'], x['value']) for x in dispatch['options']) == {'reasoningEffort': 'high', 'serviceTier': 'default'}
    assert not dispatch['hasPendingQuestion'] and not dispatch['pendingApproval']
    assert dispatch['taskId'] not in {x.get('taskId') for x in before['tasks']}
    preparation = load(N / 'brief-preparation.json')
    assert sha((P / preparation['brief']).read_bytes()) == preparation['sha256']
    for entry in load(N / 'private/completed-direct-inputs.json'):
        path = P / entry['path']
        assert sha(path.read_bytes()) == entry['sha256'] and path.stat().st_mode == entry['mode']
    now = datetime.now(timezone.utc).isoformat()
    after = copy.deepcopy(before)
    old = after['tasks'][702]
    old.update(terminal)
    old.update({'observed_utc': now, 'parent_disposition': 'PREFREEZE_NO_NOMINEE_ARCHIVED',
        'parent_intake': 'discovery-arithmetic-r162x-parent/intake.json',
        'parent_assessment': 'discovery-arithmetic-r162x-parent/assessment.md',
        'theorem_frozen': False, 'full_author_proof_submitted': False,
        'correctness_gate': None, 'contribution_gate': None, 'accepted': False, 'count_change': 0,
        'publication': 'STOPPED', 'full_diagnostic': intake['full_diagnostic'],
        'paid_comparison': intake['paid_comparison'], 'unpaid_operation': intake['unpaid_operation'],
        'status_provenance': 'Single actual notified terminal task_status receipt; detailed mathematics and limits read, exact seal and canonical bindings verified. No gate follows from artifact checks.'})
    new_index = len(after['tasks'])
    new = copy.deepcopy(dispatch)
    new.update({'observed_utc': now, 'role': 'research', 'round': 1,
        'target': {'providerInstanceId': 'codex', 'model': 'gpt-6-astra', 'options': {'reasoningEffort': 'high', 'serviceTier': 'default'}},
        'title': 'Arithmetic162y: confirmed graph-metric operative-proof discovery',
        'clientRequestId': 'twenty-20261023-fresh-arithmetic-r162y-codex-astra-r1',
        'parent_thread': '6742db91-d35c-44d0-a762-e5d9232f5177',
        'output': 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162y/',
        'brief': preparation['brief'], 'brief_sha256': preparation['sha256'], 'brief_bytes': preparation['bytes'],
        'submitted_prompt_contains_full_brief': True,
        'source_family_navigation': 'DISTINCT Source089; exact catalogue[147957,149459),two confirmed folders,29 canonical blobs/36 complete-tree entries including roots; actual build/main.tex in each. Parent metadata only.',
        'round_namespace': 'Distinct graph-metric family; full projection-body dimension-uniform diagnostic and every earlier frozen scope unchanged. Source weighted embedding/flow-cut/strong operative consequences are paid.',
        'all_previous_literal_guards_and5570_standing_bytes_retained': True,
        'dispatch_receipt': 'discovery-arithmetic-r162y-parent/dispatch.json',
        'prospective_isolation': 'discovery-arithmetic-r162y-parent/prospective-isolation.json',
        'accepted': False, 'count_change': 0, 'parent_count_at_dispatch': 19, 'publication': 'STOPPED',
        'status_provenance': 'Actual async delegate_task response; provider/model/options matched; no watcher or polling.'})
    after['tasks'].append(new)
    snapshot = after['current_work_snapshot']
    snapshot['arithmetic_r162x_archive'] = {'task_index': 702, 'status': 'PREFREEZE_NO_NOMINEE',
        'intake': 'discovery-arithmetic-r162x-parent/intake.json',
        'full_diagnostic': intake['full_diagnostic'], 'unpaid_operation': intake['unpaid_operation'],
        'correctness_gate': None, 'contribution_gate': None, 'accepted': False, 'count_change': 0}
    for field in ('t3_current_confirmed_running', 't3_last_polled_running'):
        snapshot[field] = [x for x in snapshot.get(field, []) if x != terminal['taskId']]
    snapshot['t3_current_confirmed_running'].append(new['taskId'])
    snapshot['t3_recorded_running_different_owner'] = [x for x in snapshot.get('t3_recorded_running_different_owner', []) if x.get('taskId') != terminal['taskId']]
    snapshot['arithmetic162y_prospective_isolation'] = {'task_index': new_index, 'taskId': new['taskId'],
        'brief': preparation['brief'], 'source': '089', 'catalogue_extent': [147957,149459],
        'original_brief_guards_checked_before_creation': True, 'private_local_inputs_and_metadata_retained': True,
        'status_at_dispatch': dispatch['status'], 'foreign_live_queries': False, 'publication': 'STOPPED'}
    progress = ('Arithmetic162x archived PREFREEZE/no nominee: uniform projection-body diagnostic remains unproved; '
                'O(n^5) comparison paid, same-witness dimension-uniform transfer unpaid. Distinct confirmed Source089 '
                'graph-metric discovery dispatched with full standing brief and prospective isolation. '
                'Campaign 19/20 latest R041 one remains; publication STOPPED; other records preserved without foreign live queries.')
    snapshot['observed_utc'] = now
    snapshot['note'] = progress
    after['last_parent_progress'] = progress
    changed = [i for i, (a, z) in enumerate(zip(before['tasks'], after['tasks'])) if a != z]
    assert changed == [702]
    for key in before:
        if key not in ('tasks', 'current_work_snapshot', 'last_parent_progress'):
            assert before[key] == after[key], key
    note = ('\n\n## Arithmetic162x archived; graph-metric discovery continues\n\n'
            'Arithmetic162x is PREFREEZE/no nominee. The full all-body, all-dimension projection-volume squared-asymmetry '
            'diagnostic remains unproved. The integrated source/primary comparison pays uniform scalar slack, same-position '
            'radial conversion and an O(n^5) bound; dimension-uniform transfer to the original arbitrary body retaining '
            'the same pairing, first-variation deficit and angular slack remains unpaid. No weaker result is nominated. '
            'Parent assessment: `frontier/campaigns/2026-10-14/discovery-arithmetic-r162x-parent/assessment.md`; '
            'intake: `frontier/campaigns/2026-10-14/discovery-arithmetic-r162x-parent/intake.json`. '
            'Reading limits and the disclosed whole-journal raw-byte access remain recorded; artifact checks are not mathematical gates.\n\n'
            'One distinct confirmed Source089 planar/bounded-treewidth graph-metric discovery was dispatched via '
            'Codex/GPT-6 Astra/high/default with complete standing instructions, prior scopes and prospective original-brief guards. '
            'The existing weighted embedding and flow-cut results are paid; full operative reading precedes new deductions. '
            '**19/20**, latest **R041**, one remains. No grade or count change. Publication/uploads/submissions/contacts/browser UI '
            'remain **STOPPED**. Protected bodies and named metadata stay private/local; other tasks and old scopes are unchanged.\n')
    proposed = {T: (json.dumps(after, indent=2) + '\n').encode(), J: raw[J] + note.encode()}
    assert git('rev-parse', 'HEAD').decode().strip() == head and not git('diff', '--cached', '--name-only')
    for path, content in raw.items():
        assert (P / path).read_bytes() == content
    for path, content in proposed.items():
        (P / path).write_bytes(content)
    save(D / 'integration-guard.json', {'head_before': head, 'changed_task_indices': changed,
        'appended_task_index': new_index, 'appended_taskId': new['taskId'],
        'all_other_tasks_and_top_fields_preserved': True, 'journal_prefix_preserved': True,
        'coordination_after_sha256': {path: sha(content) for path, content in proposed.items()},
        'count_change': 0, 'publication': 'STOPPED'})
    save(N / 'registration.json', {'task_index': new_index, 'taskId': new['taskId'],
        'status_at_dispatch': dispatch['status'], 'provider_model_options_verified': True,
        'count_change': 0, 'publication': 'STOPPED'})
    print(json.dumps({'result': 'INTEGRATED', 'changed_task': 702, 'appended_task': new_index,
                      'campaign': '19/20', 'next': 'Source089 discovery running', 'publication': 'STOPPED'}))


if __name__ == '__main__':
    main()
