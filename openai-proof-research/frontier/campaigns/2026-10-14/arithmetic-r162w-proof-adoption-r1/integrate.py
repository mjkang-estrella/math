#!/usr/bin/env python3
"""One-shot CAS integration of correctness only; never dispatches or commits."""
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
T = 'frontier/campaigns/2026-10-14/tasks.json'
J = 'frontier/NEW-TEN-2026-10-14.md'
REL = str(D.relative_to(P))


def git(*args):
    return subprocess.check_output(['git', *args], cwd=P)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def save(name, data):
    (D / name).write_text(json.dumps(data, indent=2) + '\n')


def main():
    assert not (D / 'integration-guard.json').exists(), 'already integrated; do not rerun'
    assert not git('diff', '--cached', '--name-only'), 'index occupied'
    base = json.loads((D / 'integration-baseline.json').read_bytes())
    for path, expected in base['protected'].items():
        assert digest((P / path).read_bytes()) == expected
    head = git('rev-parse', 'HEAD').decode().strip()
    raw = {path: git('show', f'{head}:openai-proof-research/{path}') for path in (T, J)}
    for path, content in raw.items():
        assert (P / path).read_bytes() == content, 'uncommitted coordination; defer safely'
    before = json.loads(raw[T])
    old = json.loads((D / 'private/tasks-before.json').read_bytes())
    assert before['tasks'][697:700] == old['tasks'][697:700], 'own records advanced; reconcile first'
    assert before['newAccepted'] == 19 and before['target'] == 20
    assert before['remaining'] == 1 and before['latestAcceptance'] == 'R041'
    assert len(before['tasks']) >= base['taskCount']
    new_guards = []
    for index in range(base['taskCount'], len(before['tasks'])):
        task = before['tasks'][index]
        if task.get('status') not in ('running', 'queued', 'waiting', 'starting'):
            continue
        brief = task.get('brief')
        assert brief, 'new recorded peer missing original brief; no live query'
        content = (P / brief).read_bytes()
        patterns = re.findall(r'\*[^\s,;()]*\*', content.decode())
        matches = [s for s in patterns if s not in ('*', '**')
                   and fnmatch.fnmatchcase(REL.casefold(), s.casefold())]
        assert matches, 'new original peer guards do not cover namespace'
        new_guards.append({'index': index, 'brief': brief,
                           'sha256': digest(content), 'matches': matches})
    save('coordination-rebase.json', {
        'baseline_head': base['head'], 'current_committed_head': head,
        'committed_rebase_needed': head != base['head'],
        'new_recorded_original_brief_guard_checks': new_guards,
        'no_foreign_live_query': True,
    })
    for path, content in raw.items():
        (D / 'private' / ('tasks-integration-before.json' if path == T else 'journal-integration-before.md')).write_bytes(content)

    now = datetime.now(timezone.utc).isoformat()
    terminal = json.loads((D / 'task-status.json').read_bytes())['structuredContent']
    assert terminal['status'] == 'completed' and terminal['workState'] == 'result_available'
    assert not terminal['hasPendingChildRuns'] and not terminal['hasPendingQuestion'] and not terminal['pendingApproval']
    assert terminal['taskId'] == before['tasks'][698]['taskId']
    verification = json.loads((D / 'verification.json').read_bytes())
    assert verification['result'] == 'MATCH'
    gate = 'PASS_FULL_UNCHANGED_FROZEN_R162W'
    adoption = {
        'review_task_index': 698, 'author_task_index': 697,
        'gate': gate, 'conditional_on_stipulated_upstream_truth': True,
        'entire_unchanged_frozen_statement_and_proof': True,
        'frozen_statement_sha256': before['tasks'][697]['frozen_statement_sha256'],
        'author_proof_sha256': before['tasks'][697]['author_proof_sha256'],
        'review_sha256': '9165c77ee3d715a31c511113f145c33d10cc4e61c6d2e1f742e3e5fbf7c81f51',
        'required_author_repairs': [], 'essential_correctness_obligations': [],
        'review_anchors': verification['anchors'],
        'parent_assessment': REL + '/assessment.md',
        'verification': REL + '/verification.json',
        'contribution_status': 'PENDING_NOT_POLLED_OR_INSPECTED',
        'accepted': False, 'count_change': 0, 'accepted_count': 19,
        'remaining': 1, 'latest_acceptance': 'R041', 'publication': 'STOPPED',
        'observed_utc': now,
    }
    save('adoption.json', adoption)
    after = copy.deepcopy(before)
    proof = after['tasks'][698]
    proof.update(terminal)
    proof.update({
        'observed_utc': now, 'parent_disposition': 'CORRECTNESS_PASS_ADOPTED_CONTRIBUTION_PENDING',
        'gate': gate, 'parent_adoption': REL + '/adoption.json',
        'parent_assessment': REL + '/assessment.md',
        'status_provenance': 'Single notified terminal task_status receipt, full detailed review read and unchanged inputs verified; no pending contribution or foreign live query.',
        'accepted': False, 'count_change': 0, 'publication': 'STOPPED',
    })
    author = after['tasks'][697]
    author['parent_disposition'] = 'CORRECTNESS_PASS_CONTRIBUTION_PENDING'
    author['correctness_gate'] = gate
    author['correctness_adoption'] = REL + '/adoption.json'
    author['independent_reviews']['proof'].update({'status': 'completed', 'adopted_gate': gate,
                                                 'parent_adoption': REL + '/adoption.json'})
    snapshot = after['current_work_snapshot']
    snapshot['arithmetic_r162w_nominee'].update({
        'status': 'CORRECTNESS_PASS_CONTRIBUTION_PENDING', 'correctness_gate': gate,
        'correctness_adoption': REL + '/adoption.json'})
    snapshot['arithmetic_r162w_reviews']['proof'].update({
        'status': 'completed', 'adopted_gate': gate, 'parent_adoption': REL + '/adoption.json'})
    snapshot['arithmetic_r162w_correctness_adoption'] = adoption
    for field in ('t3_last_polled_running', 't3_current_confirmed_running'):
        snapshot[field] = [x for x in snapshot.get(field, []) if x != proof['taskId']]
    snapshot['t3_recorded_running_different_owner'] = [
        x for x in snapshot.get('t3_recorded_running_different_owner', [])
        if x.get('taskId') != proof['taskId']]
    progress = ('R162W independent full correctness PASS adopted for unchanged theorem and proof, '
                'relative to stipulated upstream truth; no repair or essential correctness gap. '
                'Separate contribution review pending and unpolled. Campaign 19/20, latest R041, '
                'one remaining; no acceptance/count change; publication STOPPED. Other records preserved.')
    snapshot['observed_utc'] = now
    snapshot['note'] = progress
    after['last_parent_progress'] = progress
    changed_tasks = [i for i, (x, y) in enumerate(zip(before['tasks'], after['tasks'])) if x != y]
    assert changed_tasks == [697, 698]
    for key in before:
        if key not in ('tasks', 'current_work_snapshot', 'last_parent_progress'):
            assert before[key] == after[key], key
    assert before['tasks'][699] == after['tasks'][699]
    assert before['tasks'][697]['independent_reviews']['contribution'] == author['independent_reviews']['contribution']
    note = ('\n\n## R162W independent correctness adopted — contribution pending\n\n'
            'The parent adopts PASS for the entire unchanged frozen open critical-capacity ball '
            'embedding theorem and author proof, relative to stipulated upstream truth. '
            'The independent reconstruction identifies no required author repair or essential '
            'remaining correctness obligation. The complete review and its reading limits were read; '
            'the 158-file payload, 127 admitted author originals/copies, all 152 author-root files, '
            '55 canonical bindings and three narrow original-history extents authenticate unchanged. '
            'Integrity checks are not mathematical gates.\n\n'
            'The contribution review remains pending and uninspected. No contribution verdict, '
            'acceptance or count is assigned. Campaign **19/20**, latest **R041**, one remains. '
            'Publication/uploads remain **STOPPED**. Other task records and older scopes are unchanged. '
            f'Parent adoption: `{REL}/adoption.json`; original summary: `{REL}/assessment.md`. '
            'Source-bearing author/reviewer bodies and detailed metadata remain private/local.\n')
    proposed = {T: (json.dumps(after, indent=2) + '\n').encode(), J: raw[J] + note.encode()}
    assert git('rev-parse', 'HEAD').decode().strip() == head
    assert not git('diff', '--cached', '--name-only')
    for path, content in raw.items():
        assert (P / path).read_bytes() == content
    for path, content in proposed.items():
        (P / path).write_bytes(content)
    save('integration-guard.json', {
        'head_before': head, 'tasks_before': len(before['tasks']),
        'changed_task_indices': changed_tasks, 'pending_contribution_record_unchanged': True,
        'all_other_tasks_and_top_fields_preserved': True, 'journal_prefix_preserved': True,
        'coordination_after_sha256': {path: digest(content) for path, content in proposed.items()},
        'count_change': 0, 'publication': 'STOPPED',
    })
    print(json.dumps({'result': 'INTEGRATED', 'changed_tasks': changed_tasks,
                      'contribution': 'PENDING', 'campaign': '19/20', 'publication': 'STOPPED'}))


if __name__ == '__main__':
    main()
