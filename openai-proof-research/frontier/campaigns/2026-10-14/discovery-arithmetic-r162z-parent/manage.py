#!/usr/bin/env python3
"""One-shot committed-baseline CAS: archive r162z and register r162aa."""
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
N = B / 'discovery-arithmetic-r162aa-parent'
T, J = 'frontier/campaigns/2026-10-14/tasks.json', 'frontier/NEW-TEN-2026-10-14.md'
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
        assert (P / path).read_bytes() == content, 'uncommitted coordination; defer'
    before = json.loads(raw[T])
    initial = load(D / 'private/intake/tasks-before.json')
    assert before['tasks'][707] == initial['tasks'][707], 'own record advanced; reconcile'
    assert (before['newAccepted'], before['target'], before['remaining'], before['latestAcceptance']) == (19, 20, 1, 'R041')
    assert len(before['tasks']) >= baseline['taskCount']
    paths = load(D / 'intake-prospective-isolation.json')['namespaces']
    additional_guards = []
    for index in range(baseline['taskCount'], len(before['tasks'])):
        task = before['tasks'][index]
        if task.get('status') not in ('running', 'queued', 'waiting', 'starting'):
            continue
        content = (P / task['brief']).read_bytes()
        patterns = [s for s in re.findall(r'\*[^\s,;()]*\*', content.decode()) if s not in ('*', '**')]
        matches = {path: [s for s in patterns if fnmatch.fnmatchcase(path.casefold(), s.casefold())] for path in paths}
        assert all(matches.values()), 'new original peer guard does not cover future writes'
        additional_guards.append({'index': index, 'brief': task['brief'], 'sha256': sha(content), 'matches': matches})
    save(D / 'coordination-rebase.json', {'baseline_head': baseline['head'], 'head_before': head,
         'committed_rebase_needed': head != baseline['head'], 'new_original_brief_guard_checks': additional_guards,
         'foreign_liveness_findings_or_bodies_not_queried': True})
    for path, content in raw.items():
        (D / 'private/intake' / ('tasks-integration-before.json' if path == T else 'journal-integration-before.md')).write_bytes(content)
    terminal = load(D / 'task-status.json')['structuredContent']
    assert terminal['taskId'] == before['tasks'][707]['taskId']
    assert terminal['status'] == 'completed' and terminal['workState'] == 'result_available'
    assert not terminal['hasPendingChildRuns'] and not terminal['hasPendingQuestion'] and not terminal['pendingApproval']
    intake = load(D / 'intake.json')
    assert intake['disposition'] == 'PREFREEZE_NO_NOMINEE_ARCHIVED' and load(D / 'verification.json')['result'] == 'MATCH'
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
    after['tasks'][707].update(terminal)
    after['tasks'][707].update({'observed_utc': now, 'parent_disposition': intake['disposition'],
        'parent_intake': 'discovery-arithmetic-r162z-parent/intake.json',
        'parent_assessment': 'discovery-arithmetic-r162z-parent/assessment.md',
        'theorem_frozen': False, 'full_author_proof_submitted': False,
        'correctness_gate': None, 'contribution_gate': None, 'accepted': False, 'count_change': 0,
        'publication': 'STOPPED', 'full_diagnostic': intake['full_diagnostic'],
        'paid_comparison': intake['paid_comparison'], 'unpaid_operation': intake['unpaid_operation'],
        'status_provenance': 'Single actual notified terminal receipt; full mathematics/limits read, seal and unchanged canonical/input bindings verified. Artifact checks are not gates.'})
    new_index = len(after['tasks'])
    new = copy.deepcopy(dispatch)
    new.update({'observed_utc': now, 'role': 'research', 'round': 1,
        'target': {'providerInstanceId': 'codex', 'model': 'gpt-6-astra', 'options': {'reasoningEffort': 'high', 'serviceTier': 'default'}},
        'title': 'Arithmetic162aa: confirmed covering-density operative-proof discovery',
        'clientRequestId': 'twenty-20261023-fresh-arithmetic-r162aa-codex-astra-r1',
        'parent_thread': '6742db91-d35c-44d0-a762-e5d9232f5177',
        'output': 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162aa/',
        'brief': preparation['brief'], 'brief_sha256': preparation['sha256'], 'brief_bytes': preparation['bytes'],
        'submitted_prompt_contains_full_brief': True,
        'source_family_navigation': 'DISTINCT Source092; selected catalogue[153911,155355),two confirmed folders,27 blobs/34 complete-tree entries including roots; actual build/main.tex and build/paper.tex. Source091 body not decoded. Parent metadata only.',
        'round_namespace': 'Distinct covering-density family; full all-n two-sided spherical remainder,graph-metric,projection-body and all previous scopes unchanged. Entire source single-lattice upper and unrestricted symmetric lower n-log-n covering results are paid.',
        'all_previous_literal_guards_and5570_standing_bytes_retained': True,
        'dispatch_receipt': 'discovery-arithmetic-r162aa-parent/dispatch.json',
        'prospective_isolation': 'discovery-arithmetic-r162aa-parent/prospective-isolation.json',
        'accepted': False, 'count_change': 0, 'parent_count_at_dispatch': 19, 'publication': 'STOPPED',
        'status_provenance': 'Actual async delegate_task dispatch; provider/model/options matched; no watcher or polling.'})
    after['tasks'].append(new)
    snapshot = after['current_work_snapshot']
    snapshot['arithmetic_r162z_archive'] = {'task_index': 707, 'status': 'PREFREEZE_NO_NOMINEE',
        'intake': 'discovery-arithmetic-r162z-parent/intake.json', 'full_diagnostic': intake['full_diagnostic'],
        'unpaid_operation': intake['unpaid_operation'], 'correctness_gate': None,
        'contribution_gate': None, 'accepted': False, 'count_change': 0}
    for field in ('t3_current_confirmed_running', 't3_last_polled_running'):
        snapshot[field] = [x for x in snapshot.get(field, []) if x != terminal['taskId']]
    snapshot['t3_current_confirmed_running'].append(new['taskId'])
    snapshot['t3_recorded_running_different_owner'] = [x for x in snapshot.get('t3_recorded_running_different_owner', []) if x.get('taskId') != terminal['taskId']]
    snapshot['arithmetic162z_prospective_isolation'] = {'task_index': new_index, 'taskId': new['taskId'],
        'brief': preparation['brief'], 'source': '092', 'catalogue_extent': [153911,155355],
        'original_brief_guards_checked_before_creation': True, 'private_local_inputs_and_metadata_retained': True,
        'status_at_dispatch': dispatch['status'], 'foreign_live_queries': False, 'publication': 'STOPPED'}
    progress = 'Arithmetic162z archived PREFREEZE/no nominee: full all-n two-sided spherical remainder remains unproved; same-configuration upper heat/global-field construction unpaid. Distinct Source092 covering-density discovery dispatched with full standing instructions and prospective isolation. Campaign 19/20 latest R041 one remains; publication STOPPED. Other records preserved without foreign live queries.'
    snapshot.update({'observed_utc': now, 'note': progress})
    after['last_parent_progress'] = progress
    changed = [i for i, (a, z) in enumerate(zip(before['tasks'], after['tasks'])) if a != z]
    assert changed == [707]
    for key in before:
        if key not in ('tasks', 'current_work_snapshot', 'last_parent_progress'):
            assert before[key] == after[key], key
    note = '\n\n## Arithmetic162z archived; covering-density discovery continues\n\nArithmetic162z is PREFREEZE/no nominee. The full all-n two-sided spherical logarithmic remainder at the exact triangular coefficient remains unproved. The notebook retains same-configuration heat/global-field reduction, cardinality correction and a source-compatible curved lower comparison; one coherent upper construction retaining the same total field budget remains unpaid. No one-sided or different-coefficient substitute is nominated. Assessment: `frontier/campaigns/2026-10-14/discovery-arithmetic-r162z-parent/assessment.md`; intake: `frontier/campaigns/2026-10-14/discovery-arithmetic-r162z-parent/intake.json`. Full derivation/limits were read and 107 selection files authenticated; artifact checks are not math gates.\n\nOne distinct Source092 covering-density discovery was dispatched via Codex/GPT-6 Astra/high/default with complete standing instructions and prospective original-brief guards. Both source covering theorems are paid. Only Source092 body was selected from the two-title window; Source091 body was not decoded. **19/20**, latest **R041**, one remains. No grade/count change. Publication/uploads/submissions/contacts/browser UI remain **STOPPED**. Protected bodies/named metadata stay private/local; other tasks and all earlier scopes are unchanged.\n'
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
    print(json.dumps({'result': 'INTEGRATED', 'changed_task': 707, 'appended_task': new_index,
                      'campaign': '19/20', 'next': 'Source092 discovery running', 'publication': 'STOPPED'}))


if __name__ == '__main__':
    main()
