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
gate = 'PASS_FULL_UNCHANGED_FROZEN_STRUCTURAL198'
rel = 'discovery-structural-r198-parent/proof-r1-adoption/'
adopt = {
    'observed_utc': now, 'parent_thread': OWNER, 'task_index': 684,
    'taskId': terminal['taskId'], 'gate': gate, 'entire_unchanged_frozen_scope': True,
    'frozen_statement_sha256': '9b96245518d383432e770924856a44463c118ca68289eb7d85950acf1f872e09',
    'author_proof_sha256': '0133cd993a29c07911b198f4553121614363a4f4c5d45c2b67b10b4b60de406d',
    'review_sha256': r['review_sha256'], 'review_anchors': r['anchors'],
    'assessment_sha256': sha(P / 'assessment.md'),
    'artifact_replay': {
        'selected_files': 51, 'selected_directories': 3,
        'selected_bytes': r['selected_bytes'], 'canonical_blobs': 4,
        'primary_pdf_bindings': 5, 'reading_record_bindings': 27,
        'history_spans': 2, 'copied_controls_passed': 8,
        'exact_selection_and_modes': True, 'author_and_review_roots_unchanged': True,
    },
    'scope_includes_incomplete_normed_spaces': True,
    'reading_limits': 'Bounded primary and original-history scopes; late Geher applicability spans; no formal coverage or exhaustive contribution clearance.',
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
x = t['tasks'][684]
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
a = t['tasks'][681]
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
note = ('Structural198 full unchanged correctness PASS adopted after complete review reading and '
        '51-file exact-selection replay, including the incomplete-normed-space auxiliary theorem. '
        'Contribution pending. No count/downstream change. Foreign-owner entries preserved without '
        'liveness/body inspection. Campaign 19/20 latest R041 one remains publication STOPPED.')
s.update(observed_utc=now, note=note)
s['structural198_parent_intake'].update(disposition=intake['disposition'])
for q in s['structural198_review_dispatches']:
    if q['role'] == 'proof':
        q.update(status='completed', gate=gate)
s['structural198_correctness_adoption'] = {
    'task_index': 684, 'gate': gate, 'adoption': rel + 'adoption.json',
    'review_sha256': r['review_sha256'], 'auxiliary_incomplete_normed_spaces_included': True, 'count_change': 0,
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
    if i not in [681, 684]:
        assert t['tasks'][i] == z
assert all(t[k] == old[k] for k in old if k not in ['tasks', 'current_work_snapshot', 'last_parent_progress'])
append = '\n## Structural198 full unchanged correctness PASS; contribution pending\n\nAdopt the independent correctness review as **PASS for the entire unchanged frozen statement and author proof**, including the auxiliary theorem for arbitrary incomplete real normed spaces. Every dimension, flat faces, no assumed regularity of f, exactly two continuous odd bijective isometric lifts, even signs, uniqueness and converse are included. The Banach classification invokes stipulated Source322 at its exact ordinary-isometry interface. No essential repair, narrowing or unresolved correctness obligation remains. See [review](campaigns/2026-10-14/structural-r198-proof-r1/packet/authored/REVIEW.md) and [parent adoption](campaigns/2026-10-14/discovery-structural-r198-parent/proof-r1-adoption/assessment.md).\n\nParent read the full review and limits and verified 51 selected files, three directories, four canonical bindings, five primary PDF bindings, 27 reading-record bindings, two original-history spans and eight copied controls. Author and reviewer files remain unchanged. Exact source/primary versions and extents, late Gehér applicability reading and access recovery, CL-space/uniform-algebra omissions, historical exclusions and absence of formal coverage remain explicit. The separate contribution review is pending; no acceptance or downstream stage opens. Foreign-owner entries and earlier scopes are preserved. **19/20, latest R041, one remaining; publication stopped.**\n'
assert '## Structural198 full unchanged correctness PASS; contribution pending' not in lr.decode()
assert registry.read_bytes() == raw and ledger.read_bytes() == lr and ip.read_bytes() == ir
rt = registry.with_suffix('.structural198-proof.tmp')
rt.write_text(json.dumps(t, indent=2) + '\n')
assert registry.read_bytes() == raw
os.replace(rt, registry)
assert ledger.read_bytes() == lr
ledger.write_bytes(lr + append.encode())
assert ip.read_bytes() == ir
ip.write_text(json.dumps(intake, indent=2) + '\n')
out = {'observed_utc': now, 'correctness': gate, 'contribution': 'PENDING',
       'count': 19, 'modified_task_indices': [681, 684], 'old_task_count': len(old['tasks']),
       'all_other_task_entries_unchanged': True, 'active_indices': active}
(P / 'integration-record.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
