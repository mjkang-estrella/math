#!/usr/bin/env python3
"""Integrate this owner's completed nominee and two independent review dispatches."""
import copy
import datetime
import hashlib
import json
from pathlib import Path

P = Path(__file__).resolve().parent
C = P.parent
OWNER = '164b1204-be68-4540-94bb-0b91055c4381'
NOW = datetime.datetime.now(datetime.timezone.utc).isoformat()

def read(p):
    return json.loads(p.read_text())

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def dump(p, value):
    p.write_text(json.dumps(value, indent=2) + '\n')

path = C / 'tasks.json'
original_bytes = path.read_bytes()
t = json.loads(original_bytes)
before = copy.deepcopy(t)
tasks = t['tasks']
assert tasks[655]['parent_thread'] == OWNER
assert not tasks[655].get('parent_disposition')
terminal = read(P / 'task-status.json')
assert terminal['status'] == 'completed' and terminal['taskId'] == tasks[655]['taskId']
for key in ('status', 'workState', 'hasPendingChildRuns', 'latestTerminalRunId',
            'latestTerminalStatus', 'latestTerminalSummary', 'latestTerminalResultContextTransferId',
            'summary', 'resultContextTransferId', 'hasPendingQuestion', 'pendingApproval', 'waitTimedOut'):
    tasks[655][key] = terminal[key]
verification = read(P / 'resume-verification.json')
frozen = verification['frozen']
tasks[655].update(parent_disposition='FULL_AUTHOR_PROOF_NOMINEE_REVIEWS_PENDING',
                  parent_full_intake_pending=False, parent_intake_utc=NOW,
                  parent_intake='discovery-structural-r195-parent/intake.json',
                  parent_assessment_sha256=sha(P / 'assessment.md'),
                  frozen_scope_sha256=frozen['sha256'],
                  author_proof_sha256=frozen['author_proof_sha256'],
                  correctness='REVIEW_PENDING', contribution='REVIEW_PENDING',
                  accepted=False, count_change=0)
reviews = []
for role in ('proof', 'contribution'):
    receipt = read(P / f'dispatch-{role}-r1.json')
    assert not any(x.get('clientRequestId') == receipt['clientRequestId'] for x in tasks)
    assert receipt['providerInstanceId'] == 'codex' and receipt['model'] == 'gpt-6-astra'
    assert receipt['options'] == [{'id': 'reasoningEffort', 'value': 'high'}, {'id': 'serviceTier', 'value': 'default'}]
    brief = verification['briefs'][role]
    assert sha(C / brief['path']) == brief['sha256']
    entry = copy.deepcopy(receipt)
    entry.update(role='review', review_role=role, round=1, nominee='Structural195',
                 author_task_index=655, output='frontier/campaigns/2026-10-14/' + brief['output'] + '/',
                 brief='frontier/campaigns/2026-10-14/' + brief['path'],
                 brief_sha256=brief['sha256'], brief_bytes=brief['bytes'],
                 target={'providerInstanceId': 'codex', 'model': 'gpt-6-astra',
                         'options': {'reasoningEffort': 'high', 'serviceTier': 'default'}},
                 parent_count_at_dispatch=19, accepted=False, count_change=0, publication='STOPPED',
                 dispatch_receipt=f'discovery-structural-r195-parent/dispatch-{role}-r1.json',
                 prospective_isolation='discovery-structural-r195-parent/prospective-isolation.json')
    index = len(tasks)
    tasks.append(entry)
    reviews.append({'task_index': index, 'role': role, 'taskId': entry['taskId'],
                    'status': entry['status'], 'brief': brief})

intake = {'observed_utc': NOW, 'nominee': 'Structural195', 'author_task_index': 655,
          'author_taskId': tasks[655]['taskId'], 'parent_thread': OWNER,
          'parent_disposition': 'FULL_AUTHOR_PROOF_NOMINEE_REVIEWS_PENDING',
          'frozen': frozen, 'assessment': 'assessment.md', 'assessment_sha256': sha(P / 'assessment.md'),
          'questions': 'questions.md', 'questions_sha256': sha(P / 'questions.md'),
          'author_terminal_receipt': 'task-status.json', 'prior_replay': 'replay.json',
          'resume_verification': 'resume-verification.json',
          'author_root_bytes_modes_unchanged': True,
          'artifact_checks_are_not_mathematical_gates': True,
          'correctness': 'REVIEW_PENDING', 'contribution': 'REVIEW_PENDING',
          'contribution_correctness_condition': 'UNDISCHARGED',
          'review_dispatches': reviews, 'accepted': False, 'count_change': 0,
          'newAccepted': 19, 'remaining': 1, 'latestAcceptance': 'R041', 'publication': 'STOPPED',
          'downstream': 'NOT_STARTED_GATES_NOT_MET', 'no_new_structural_discovery_dispatched': True,
          'integration': 'INTEGRATED'}
s = t['current_work_snapshot']
s['observed_utc'] = NOW
s['active_task_indices'] = [i for i, x in enumerate(tasks)
                            if x.get('parent_thread') and x.get('taskId')
                            and x.get('status') in ('running', 'queued', 'waiting')]
s['t3_last_polled_running'] = [x['taskId'] for x in reviews]
s['t3_last_polled_running_note'] = 'This owner confirmed both Structural195 reviews running at dispatch; foreign task liveness is shared-ledger metadata only.'
s['t3_recorded_running_different_owner'] = [
    {'task_index': i, 'taskId': tasks[i]['taskId'], 'parent_thread': tasks[i].get('parent_thread'),
     'shared_record_status': tasks[i]['status'], 'current_liveness_verified_here': False,
     'current_thread_status_request': 'not_requested_foreign_owner',
     'action': 'Preserved without polling, steering, duplicate dispatch or body inspection.'}
    for i in s['active_task_indices'] if tasks[i].get('parent_thread') != OWNER]
s['structural195_parent_intake'] = {'disposition': intake['parent_disposition'],
                                  'intake': 'discovery-structural-r195-parent/intake.json',
                                  'assessment_sha256': intake['assessment_sha256'], 'count_change': 0}
s['structural195_review_dispatches'] = reviews
s['structural195_review_isolation'] = 'discovery-structural-r195-parent/prospective-isolation.json'
s['note'] = ('Structural195(idx655) completed with a frozen full author-proof nominee: a countable independent '
             'family of exact-fp-type-two spectra relative to stipulated Source319. Original statement and proof '
             'remain unchanged; saved replay and fresh 73-file verification match. Independent full-scope '
             'correctness and conditional contribution reviews dispatched under Codex/Astra high/default. '
             'No mathematical grade, acceptance or count adopted. Foreign-owner entries preserved. '
             'Campaign19/20, latestR041, one remains; publication STOPPED.')
t['last_parent_progress'] = s['note']
for i, old in enumerate(before['tasks']):
    if i != 655:
        assert tasks[i] == old, i
changed_snapshot = {'observed_utc', 'active_task_indices', 't3_last_polled_running',
                    't3_last_polled_running_note', 't3_recorded_running_different_owner',
                    'structural195_parent_intake', 'structural195_review_dispatches',
                    'structural195_review_isolation', 'note'}
for key, value in before['current_work_snapshot'].items():
    if key not in changed_snapshot:
        assert s[key] == value, key
for key, value in before.items():
    if key not in ('tasks', 'current_work_snapshot', 'last_parent_progress'):
        assert t[key] == value, key
assert (t['newAccepted'], t['latestAcceptance'], t['remaining']) == (19, 'R041', 1)
assert path.read_bytes() == original_bytes, 'Concurrent ledger update: rerun before writing.'
dump(path, t)
dump(P / 'intake.json', intake)
ledger = C.parents[1] / 'NEW-TEN-2026-10-14.md'
body = ledger.read_text()
heading = '## Structural195 frozen nominee; independent full-scope reviews dispatched'
assert heading not in body
entry = ('\n' + heading + '\n\n'
         'The resumed owner intake preserves the unchanged frozen statement (SHA256 ' + frozen['sha256'] +
         ') and complete author proof (SHA256 ' + frozen['author_proof_sha256'] + '). '
         'The nominee asserts countably many mutually thick-independent exact-fp-type-two spectra relative '
         'to the standard BP⟨2⟩ quotient at the frozen large-prime operator range, with both localization '
         'comparisons and the stated power-set embedding/finite-generation consequences. '
         'These are author claims, not accepted conclusions. See [assessment](campaigns/2026-10-14/'
         'discovery-structural-r195-parent/assessment.md) and [review questions](campaigns/2026-10-14/'
         'discovery-structural-r195-parent/questions.md).\n\n'
         'The pre-interruption read-only replay and finite bookkeeping checks are retained; fresh verification '
         'matched all 73 selected files and the entire saved root bytes/modes. Independent correctness review '
         '(idx' + str(reviews[0]['task_index']) + ') and contribution review conditional on correctness '
         '(idx' + str(reviews[1]['task_index']) + ') now run with Codex/gpt-6-astra/high/default. '
         'Both briefs were finalized before either dispatch and exclude the other role and the entire '
         'Arithmetic162 namespace. The foreign peer original brief contains the prospective Structural195 '
         'guard; no foreign task status or mathematical body was read. The shared ledger updates only this '
         'owner’s nominee and new reviews. No new structural discovery or downstream stage opens. '
         '**19/20, latest R041, one remaining; no grade/count change; publication stopped.**\n')
assert ledger.read_text() == body
ledger.write_text(body + entry)
print(json.dumps({'reviews': reviews, 'active_indices': s['active_task_indices'], 'count': t['newAccepted']}, indent=2))
