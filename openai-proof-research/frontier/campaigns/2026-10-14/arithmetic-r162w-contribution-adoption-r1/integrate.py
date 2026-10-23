#!/usr/bin/env python3
"""One-shot CAS: adopt the completed contribution gate and register new child."""
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
N = B / 'discovery-arithmetic-r162x-parent'
T = 'frontier/campaigns/2026-10-14/tasks.json'
J = 'frontier/NEW-TEN-2026-10-14.md'
git = lambda *args: subprocess.check_output(['git', *args], cwd=P)
load = lambda path: json.loads(path.read_bytes())
sha = lambda raw: hashlib.sha256(raw).hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def main():
    assert not (D / 'integration-guard.json').exists(), 'one-shot integration already used'
    assert not git('diff', '--cached', '--name-only'), 'occupied index'
    baseline = load(D / 'integration-baseline.json')
    for path, expected in baseline['protected'].items():
        assert sha((P / path).read_bytes()) == expected
    head = git('rev-parse', 'HEAD').decode().strip()
    raw = {path: git('show', f'{head}:openai-proof-research/{path}') for path in (T, J)}
    for path, content in raw.items():
        assert (P / path).read_bytes() == content, 'uncommitted coordination; defer'
    before = json.loads(raw[T])
    initial = load(D / 'private/tasks-before.json')
    assert before['tasks'][697:700] == initial['tasks'][697:700], 'own records advanced; reconcile'
    assert (before['newAccepted'], before['target'], before['remaining'], before['latestAcceptance']) == (19, 20, 1, 'R041')
    assert len(before['tasks']) >= baseline['taskCount']
    namespaces = [str(D.relative_to(P)), str(N.relative_to(P)),
                  'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162x',
                  'frontier/campaigns/2026-10-14/expanded-target-2026-10-17/fresh-arithmetic-r162x-brief.txt']
    extra_guards = []
    for index in range(baseline['taskCount'], len(before['tasks'])):
        task = before['tasks'][index]
        if task.get('status') not in ('running', 'queued', 'waiting', 'starting'):
            continue
        brief = task['brief']
        content = (P / brief).read_bytes()
        patterns = [s for s in re.findall(r'\*[^\s,;()]*\*', content.decode()) if s not in ('*', '**')]
        matches = {path: [s for s in patterns if fnmatch.fnmatchcase(path.casefold(), s.casefold())]
                   for path in namespaces}
        assert all(matches.values()), 'new original peer guards do not cover future writes'
        extra_guards.append({'index': index, 'brief': brief, 'sha256': sha(content), 'matches': matches})
    save(D / 'coordination-rebase.json', {'baseline_head': baseline['head'], 'head_before': head,
         'committed_rebase_needed': head != baseline['head'], 'new_original_brief_guard_checks': extra_guards,
         'no_foreign_live_query': True})
    for path, content in raw.items():
        (D / 'private' / ('tasks-integration-before.json' if path == T else 'journal-integration-before.md')).write_bytes(content)

    adoption = load(D / 'adoption.json')
    assert adoption['correctness_condition'] == 'DISCHARGED'
    receipt = load(D / 'task-status.json')['structuredContent']
    assert receipt['status'] == 'completed' and receipt['workState'] == 'result_available'
    assert not receipt['hasPendingChildRuns'] and not receipt['hasPendingQuestion'] and not receipt['pendingApproval']
    assert receipt['taskId'] == before['tasks'][699]['taskId']
    dispatch = load(N / 'dispatch.json')['structuredContent']
    assert dispatch['providerInstanceId'] == 'codex' and dispatch['model'] == 'gpt-6-astra'
    assert dict((x['id'], x['value']) for x in dispatch['options']) == {'reasoningEffort': 'high', 'serviceTier': 'default'}
    assert not dispatch['hasPendingQuestion'] and not dispatch['pendingApproval']
    assert dispatch['taskId'] not in {t.get('taskId') for t in before['tasks']}
    prepared = load(N / 'brief-preparation.json')
    assert sha((P / prepared['brief']).read_bytes()) == prepared['sha256']
    for entry in load(N / 'private/completed-direct-inputs.json'):
        path = P / entry['path']
        assert sha(path.read_bytes()) == entry['sha256'] and path.stat().st_mode == entry['mode']
    now = datetime.now(timezone.utc).isoformat()
    after = copy.deepcopy(before)
    gate = adoption['gate']
    author = after['tasks'][697]
    author.update({'parent_disposition': 'CLOSED_PASS_TECHNICAL_CONDITION_DISCHARGED_ZERO_COUNT',
                   'contribution_gate': gate, 'contribution_condition': 'DISCHARGED',
                   'contribution_adoption': str((D / 'adoption.json').relative_to(P)),
                   'accepted': False, 'count_change': 0})
    author['independent_reviews']['contribution'].update({'status': 'completed', 'adopted_gate': gate,
        'condition': 'DISCHARGED', 'parent_adoption': str((D / 'adoption.json').relative_to(P))})
    contribution = after['tasks'][699]
    contribution.update(receipt)
    contribution.update({'observed_utc': now, 'gate': gate, 'condition': 'DISCHARGED',
        'parent_disposition': 'TECHNICAL_CONDITION_DISCHARGED_NOT_ACCEPTED',
        'parent_adoption': str((D / 'adoption.json').relative_to(P)),
        'accepted': False, 'count_change': 0, 'publication': 'STOPPED',
        'status_provenance': 'One notified terminal task_status receipt; complete detailed review/limits read, exact selection and unchanged original inputs verified. No foreign live query.'})
    new_index = len(after['tasks'])
    new = copy.deepcopy(dispatch)
    new.update({'observed_utc': now, 'target': {'providerInstanceId': 'codex', 'model': 'gpt-6-astra',
        'options': {'reasoningEffort': 'high', 'serviceTier': 'default'}}, 'role': 'research',
        'title': 'Arithmetic162x: confirmed projection-body operative-proof discovery',
        'clientRequestId': 'twenty-20261023-fresh-arithmetic-r162x-codex-astra-r1',
        'round': 1, 'parent_thread': '6742db91-d35c-44d0-a762-e5d9232f5177',
        'output': 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162x/',
        'brief': prepared['brief'], 'brief_sha256': prepared['sha256'], 'brief_bytes': prepared['bytes'],
        'submitted_prompt_contains_full_brief': True, 'source_family_navigation': 'DISTINCT Source088; exact catalogue[146530,147957), two confirmed companion folders, 15 blobs/21 tree entries including roots; actual nested build/latex/main.tex and build/main.tex. Parent metadata only.',
        'round_namespace': 'Distinct family; R162W whole-scope PASS/TECHNICAL is closed with correctness condition discharged and zero count. No grade-shopping or old-target restriction.',
        'dispatch_receipt': 'discovery-arithmetic-r162x-parent/dispatch.json',
        'prospective_isolation': 'discovery-arithmetic-r162x-parent/prospective-isolation.json',
        'all_previous_literal_guards_and5570_standing_bytes_retained': True,
        'accepted': False, 'count_change': 0, 'parent_count_at_dispatch': 19, 'publication': 'STOPPED',
        'status_provenance': 'Actual async delegate_task response; no watcher or polling; actual provider/model/options matched.'})
    after['tasks'].append(new)
    snapshot = after['current_work_snapshot']
    snapshot['arithmetic_r162w_nominee'].update({'status': 'CLOSED_PASS_TECHNICAL_CONDITION_DISCHARGED_ZERO_COUNT',
        'contribution_gate': gate, 'contribution_condition': 'DISCHARGED',
        'contribution_adoption': str((D / 'adoption.json').relative_to(P))})
    snapshot['arithmetic_r162w_reviews']['contribution'].update({'status': 'completed', 'adopted_gate': gate,
        'condition': 'DISCHARGED', 'parent_adoption': str((D / 'adoption.json').relative_to(P))})
    snapshot['arithmetic_r162w_contribution_adoption'] = adoption
    for field in ('t3_current_confirmed_running', 't3_last_polled_running'):
        snapshot[field] = [x for x in snapshot.get(field, []) if x != receipt['taskId']]
    snapshot['t3_current_confirmed_running'].append(new['taskId'])
    snapshot['t3_recorded_running_different_owner'] = [x for x in snapshot.get('t3_recorded_running_different_owner', []) if x.get('taskId') != receipt['taskId']]
    snapshot['arithmetic162x_prospective_isolation'] = {'task_index': new_index, 'taskId': new['taskId'],
        'brief': prepared['brief'], 'source': '088', 'catalogue_extent': [146530, 147957],
        'original_brief_guards_checked_before_creation': True, 'private_local_inputs_and_metadata_retained': True,
        'status_at_dispatch': dispatch['status'], 'foreign_liveness_or_bodies_not_queried': True,
        'publication': 'STOPPED'}
    progress = ('R162W full unchanged correctness PASS / contribution TECHNICAL adopted, condition discharged, zero count. '
                'Distinct confirmed Source088 projection-body discovery dispatched with complete standing brief and prospective isolation. '
                'Campaign 19/20, latest R041, one remains; publication STOPPED. Other records preserved without foreign live queries.')
    snapshot['observed_utc'] = now
    snapshot['note'] = progress
    after['last_parent_progress'] = progress
    changed = [i for i, (a, z) in enumerate(zip(before['tasks'], after['tasks'])) if a != z]
    assert changed == [697, 699]
    for key in before:
        if key not in ('tasks', 'current_work_snapshot', 'last_parent_progress'):
            assert before[key] == after[key], key
    assert before['tasks'][698] == after['tasks'][698]
    note = ('\n\n## R162W closed PASS / TECHNICAL; distinct discovery continues\n\n'
            'The parent adopts TECHNICAL for the entire unchanged frozen open critical-ball theorem. '
            'Its condition is DISCHARGED by the already adopted full correctness PASS. The complete '
            'comparison supplies the compatible source/classical parameterization and gluing at the full scope; '
            'no essential contribution-comparison obligation remains. No acceptance or count follows. '
            f'Parent adoption: `{D.relative_to(P)}/adoption.json`; original assessment: `{D.relative_to(P)}/assessment.md`. '
            'The 160-file/33-directory packet and unchanged admitted author inputs authenticate; artifact integrity is not a mathematical gate. '
            'Private source-bearing packets and metadata retain original rights.\n\n'
            'One distinct Source088 projection-body discovery is now registered using Codex/GPT-6 Astra/high/default, '
            'the complete standing brief and prospective original-peer-brief guards. Both actual companion wrappers were confirmed '
            'from the complete tree; full operative/primary/original reading precedes any new deduction. '
            'No restricted retry, self-gate or downstream work is authorized. '
            '**19/20**, latest **R041**, one remains. Publication/uploads/submissions/contacts/browser UI remain **STOPPED**. '
            'Other task entries and older scopes are unchanged.\n')
    proposed = {T: (json.dumps(after, indent=2) + '\n').encode(), J: raw[J] + note.encode()}
    assert git('rev-parse', 'HEAD').decode().strip() == head and not git('diff', '--cached', '--name-only')
    for path, content in raw.items():
        assert (P / path).read_bytes() == content
    for path, content in proposed.items():
        (P / path).write_bytes(content)
    save(D / 'integration-guard.json', {'head_before': head, 'changed_task_indices': changed,
        'appended_task_index': new_index, 'appended_taskId': new['taskId'],
        'all_other_tasks_and_top_fields_preserved': True, 'correctness_record_unchanged': True,
        'journal_prefix_preserved': True, 'count_change': 0, 'publication': 'STOPPED',
        'coordination_after_sha256': {path: sha(content) for path, content in proposed.items()}})
    save(N / 'registration.json', {'task_index': new_index, 'taskId': new['taskId'],
        'status_at_dispatch': dispatch['status'], 'provider_model_options_verified': True,
        'count_change': 0, 'publication': 'STOPPED'})
    print(json.dumps({'result': 'INTEGRATED', 'changed_tasks': changed, 'appended_task': new_index,
                      'campaign': '19/20', 'R162W': 'PASS/TECHNICAL CONDITION DISCHARGED ZERO',
                      'next': 'Source088 discovery running', 'publication': 'STOPPED'}))


if __name__ == '__main__':
    main()
