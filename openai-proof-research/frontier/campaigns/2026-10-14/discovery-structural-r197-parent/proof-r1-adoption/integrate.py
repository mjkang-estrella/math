#!/usr/bin/env python3
"""Adopt this completed correctness review only; preserve every other task."""
from pathlib import Path
import copy, datetime, hashlib, json, os

P = Path(__file__).resolve().parent
C = P.parents[1]
PROJECT = C.parents[2]
OWNER = '164b1204-be68-4540-94bb-0b91055c4381'
read = lambda p: json.loads(p.read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
r = read(P / 'replay.json')
terminal = read(P / 'task-status.json')
assert terminal['status'] == 'completed' and not terminal['hasPendingChildRuns']
assert r['author_and_reviewer_bytes_modes_unchanged']
gate = 'PASS_FULL_UNCHANGED_FROZEN_STRUCTURAL197'
rel = 'discovery-structural-r197-parent/proof-r1-adoption/'
adopt = {
    'observed_utc': now, 'parent_thread': OWNER, 'task_index': 679,
    'taskId': terminal['taskId'], 'gate': gate, 'entire_unchanged_frozen_scope': True,
    'frozen_statement_sha256': '8030aa7c2a40a2b3cf5a3cfd6eacb6c78acd7984fad6d3ee0de7c3de2657537d',
    'author_proof_sha256': '8196eceec11a0b71f03dc4dd31744300dc3601a0c623ac2e1145d84ebf4d231e',
    'review_sha256': r['review_sha256'], 'review_anchors': r['anchors'],
    'assessment_sha256': sha(P / 'assessment.md'),
    'artifact_replay': {
        'selected_files': 86, 'selected_directories': 13,
        'selected_bytes': r['selected_bytes'], 'canonical_blobs': 10,
        'primary_texts': 5, 'primary_images': 11, 'primary_extraction_receipts': 5,
        'history_spans': 20, 'direct_inputs': 8, 'copied_controls_passed': 9,
        'exact_selection_and_modes': True, 'author_and_review_roots_unchanged': True,
    },
    'access_limit': r['reviewer_access_lapse_preserved'],
    'procedural_compliance': 'Strict initial byte-selection violated; disclosed, not erased. No extra journal semantic use or peer-review exposure identified.',
    'necessary_repairs': [], 'unresolved_correctness_obligations': [],
    'contribution_gate': 'PENDING',
    'correctness_prerequisite': 'SATISFIED_ON_IDENTICAL_FROZEN_STATEMENT_AND_PROOF',
    'accepted': False, 'count_change': 0, 'newAccepted': 19,
    'latestAcceptance': 'R041', 'remaining': 1, 'publication': 'STOPPED',
}
(P / 'adoption.json').write_text(json.dumps(adopt, indent=2) + '\n')

registry = C / 'tasks.json'
ledger = PROJECT / 'frontier/NEW-TEN-2026-10-14.md'
ip = P.parent / 'intake.json'
raw = registry.read_bytes()
t = json.loads(raw)
old = copy.deepcopy(t)
lr = ledger.read_bytes()
ir = ip.read_bytes()
intake = json.loads(ir)
assert (t['newAccepted'], t['latestAcceptance'], t['remaining']) == (19, 'R041', 1)
x = t['tasks'][679]
assert x['taskId'] == terminal['taskId'] and x['parent_thread'] == OWNER
assert x['status'] == 'running'
for k in ['status', 'workState', 'hasPendingChildRuns', 'latestTerminalRunId',
          'latestTerminalStatus', 'latestTerminalSummary', 'latestTerminalResultContextTransferId',
          'summary', 'resultContextTransferId', 'hasPendingQuestion', 'pendingApproval',
          'waitTimedOut', 'observed_utc']:
    x[k] = terminal[k]
x.update(parent_disposition=gate, correctness='PASS', entire_unchanged_frozen_scope=True,
         parent_full_intake_pending=False, parent_adoption=rel + 'adoption.json',
         parent_intake_utc=now, accepted=False, count_change=0,
         status_provenance='Single terminal query after completion notification; full parent intake adopted.')
a = t['tasks'][677]
assert a['parent_thread'] == OWNER
a.update(parent_disposition='CORRECTNESS_PASS_CONTRIBUTION_PENDING', correctness='PASS',
         correctness_adoption=rel + 'adoption.json', accepted=False, count_change=0)
intake.update(disposition='CORRECTNESS_PASS_CONTRIBUTION_PENDING', correctness_gate=gate,
              contribution_gate='PENDING', contribution_condition='DISCHARGED',
              correctness_review_adoption=rel + 'adoption.json',
              correctness_review_sha256=r['review_sha256'], correctness_adopted_utc=now,
              next='Await independent contribution review; no new structural discovery or downstream work while pending.')
for q in intake['reviews']:
    if q['role'] == 'proof':
        q.update(status='completed', gate=gate)
s = t['current_work_snapshot']
note = ('Structural197 full unchanged correctness PASS adopted after complete review reading and '
        '86-file exact-selection replay; initial acceptance byte-selection lapse disclosed and retained. '
        'Contribution pending. No count/downstream change. Foreign-owner entries preserved without '
        'liveness/body inspection. Campaign 19/20 latest R041 one remains publication STOPPED.')
s.update(observed_utc=now, note=note)
s['structural197_parent_intake'].update(disposition=intake['disposition'])
for q in s['structural197_review_dispatches']:
    if q['role'] == 'proof':
        q.update(status='completed', gate=gate)
s['structural197_correctness_adoption'] = {
    'task_index': 679, 'gate': gate, 'adoption': rel + 'adoption.json',
    'review_sha256': r['review_sha256'], 'access_scope_lapse_disclosed': True, 'count_change': 0,
}
active = [i for i, z in enumerate(t['tasks']) if z.get('parent_thread') and z.get('taskId')
          and z.get('status') in ['running', 'queued', 'waiting']]
s['active_task_indices'] = active
s['t3_last_polled_running'] = [t['tasks'][i]['taskId'] for i in active if t['tasks'][i]['parent_thread'] == OWNER]
s['t3_last_polled_running_note'] = ('Remaining owned task recorded running at original dispatch only; '
                                  'no sibling poll. Completed correctness task queried once after notification.')
s['t3_recorded_running_different_owner'] = [
    {'task_index': i, 'taskId': t['tasks'][i]['taskId'], 'parent_thread': t['tasks'][i]['parent_thread'],
     'shared_record_status': t['tasks'][i]['status'], 'current_liveness_verified_here': False,
     'action': 'Preserved from shared registry; no status/body inspection or steering.'}
    for i in active if t['tasks'][i]['parent_thread'] != OWNER]
t['last_parent_progress'] = note
for i, z in enumerate(old['tasks']):
    if i not in [677, 679]:
        assert t['tasks'][i] == z
assert all(t[k] == old[k] for k in old if k not in ['tasks', 'current_work_snapshot', 'last_parent_progress'])
append = '''
## Structural197 full unchanged correctness PASS; contribution pending

Adopt the independent correctness review as **PASS for the entire unchanged frozen statement and author proof**, relative to stipulated upstream truth. The review covers every m >= 3 and rank r >= 1, all complex representations and specified left modules, every connected finite cover, the explicit cyclic cover and marked torsion, and the obstruction to a finite two-dimensional model. No essential repair, narrowing or unresolved correctness obligation remains. See [review](campaigns/2026-10-14/structural-r197-proof-r1/packet/REVIEW.txt) and [parent adoption](campaigns/2026-10-14/discovery-structural-r197-parent/proof-r1-adoption/assessment.md).

Parent read the full review and limits, verified all 86 selected files and 13 directories, ten canonical bindings, five primary texts/extraction receipts, eleven images, twenty exact history spans, eight direct inputs and nine tiny copied controls. Author and reviewer roots remained unchanged. The reviewer's initial whole-file acceptance-byte load violated strict selection; only the permitted span was decoded/displayed, with no reported use of other journal text. This lapse and incidental tree-title navigation remain explicit and are not erased by later verification. The independent contribution review is pending; no acceptance or downstream stage opens. Foreign-owner entries and earlier scopes are preserved. **19/20, latest R041, one remaining; publication stopped.**
'''
assert '## Structural197 full unchanged correctness PASS; contribution pending' not in lr.decode()
assert registry.read_bytes() == raw and ledger.read_bytes() == lr and ip.read_bytes() == ir
rt = registry.with_suffix('.structural197-proof.tmp')
rt.write_text(json.dumps(t, indent=2) + '\n')
assert registry.read_bytes() == raw
os.replace(rt, registry)
assert ledger.read_bytes() == lr
ledger.write_bytes(lr + append.encode())
assert ip.read_bytes() == ir
ip.write_text(json.dumps(intake, indent=2) + '\n')
out = {'observed_utc': now, 'correctness': gate, 'contribution': 'PENDING',
       'count': 19, 'modified_task_indices': [677, 679], 'old_task_count': len(old['tasks']),
       'all_other_task_entries_unchanged': True, 'active_indices': active}
(P / 'integration-record.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
