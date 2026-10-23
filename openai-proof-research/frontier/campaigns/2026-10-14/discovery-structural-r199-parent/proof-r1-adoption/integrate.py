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
gate = 'PASS_FULL_UNCHANGED_FROZEN_STRUCTURAL199'
rel = 'discovery-structural-r199-parent/proof-r1-adoption/'
adopt = {
    'observed_utc': now, 'parent_thread': OWNER, 'task_index': 689,
    'taskId': terminal['taskId'], 'gate': gate, 'entire_unchanged_frozen_scope': True,
    'frozen_statement_sha256': '509645cdcabf8bf700027acb5ed1edff6d064b631fbfd6fe0b487b010994e229',
    'author_proof_sha256': 'aca7f9a004f6fef993bb3567dc7913a3bd032d10bab35ce9319155fd45374399',
    'review_sha256': r['review_sha256'], 'review_anchors': r['anchors'],
    'assessment_sha256': sha(P / 'assessment.md'),
    'artifact_replay': {
        'selected_files': 67, 'selected_directories': 10, 'selected_bytes': r['selected_bytes'],
        'canonical_blobs': 14, 'source_text_bindings': 13, 'primary_pdf_bindings_to_author': 6,
        'primary_text_span_bindings': 9, 'primary_images': 5, 'submission_bindings': 9,
        'history_spans': 6, 'copied_controls_passed': 5,
        'exact_selection_and_modes': True, 'author_and_review_roots_unchanged': True,
    },
    'scope_includes_every_final_subspace_and_fixed_continuum_consistency': True,
    'reading_limits': 'Bounded primary and original-history scopes, visual JR reading, inherited Saxon/Brech failures, recovered displays and late version prefixes; no formal coverage or exhaustive contribution clearance.',
    'necessary_repairs': [], 'unresolved_correctness_obligations': [],
    'contribution_gate': 'PENDING',
    'correctness_prerequisite': 'SATISFIED_ON_IDENTICAL_FROZEN_STATEMENT_AND_PROOF',
    'accepted': False, 'count_change': 0, 'newAccepted': 19,
    'latestAcceptance': 'R041', 'remaining': 1, 'publication': 'STOPPED',
}
for filename, key in [('frozen-statement.md', 'frozen_statement_sha256'), ('author-proof.md', 'author_proof_sha256')]:
    assert sha(C / 'fresh-structural-discovery-r199' / filename) == adopt[key]
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
x = t['tasks'][689]
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
a = t['tasks'][687]
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
note = ('Structural199 entire unchanged correctness PASS adopted after complete review reading and '
        '67-file exact-selection replay, including every final subspace, both fields/densities and all frozen consistency clauses. '
        'Contribution pending. No count/downstream change. Foreign-owner entries preserved without '
        'liveness/body inspection. Campaign 19/20 latest R041 one remains publication STOPPED.')
s.update(observed_utc=now, note=note)
s['structural199_parent_intake'].update(disposition=intake['disposition'])
for q in s['structural199_review_dispatches']:
    if q['role'] == 'proof':
        q.update(status='completed', gate=gate)
s['structural199_correctness_adoption'] = {
    'task_index': 689, 'gate': gate, 'adoption': rel + 'adoption.json',
    'review_sha256': r['review_sha256'], 'all_frozen_construction_and_consistency_clauses_included': True, 'count_change': 0,
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
    if i not in [687, 689]:
        assert t['tasks'][i] == z
assert all(t[k] == old[k] for k in old if k not in ['tasks', 'current_work_snapshot', 'last_parent_progress'])
append = '\n## Structural199 full unchanged correctness PASS; contribution pending\n\nAdopt the independent correctness review as **PASS for the entire unchanged frozen T323C199 statement and author proof**, under stipulated Source323 truth. Every uncountable Cohen extension, every final separable subspace, the stronger preselected path-family assertion and exact separation constant, both operator interfaces, all closed quotient kernels, both fields and both densities, and all frozen fixed-continuum consistency clauses are included. No essential repair, narrowing or unresolved correctness obligation remains. See [review](campaigns/2026-10-14/structural-r199-proof-r1/REVIEW.md) and [parent adoption](campaigns/2026-10-14/discovery-structural-r199-parent/proof-r1-adoption/assessment.md).\n\nParent read the complete independent review and limits and verified 67 selected files, ten directories, 14 canonical bindings, 13 source text bindings, six primary PDF receipts to retained author originals, nine primary text spans, five scan images, nine submission bindings, six original-history spans and five copied controls. All author and reviewer bytes and modes remain unchanged. Exact reading extents, recovered displays, late version checks, inherited primary access failures, historical exclusions and absence of formal coverage remain explicit. The separate contribution review is pending; no acceptance or downstream stage opens. Foreign-owner entries and earlier scopes are preserved. **19/20, latest R041, one remaining; publication stopped.**\n'
assert '## Structural199 full unchanged correctness PASS; contribution pending' not in lr.decode()
assert registry.read_bytes() == raw and ledger.read_bytes() == lr and ip.read_bytes() == ir
rt = registry.with_suffix('.structural199-proof.tmp')
rt.write_text(json.dumps(t, indent=2) + '\n')
assert registry.read_bytes() == raw
os.replace(rt, registry)
assert ledger.read_bytes() == lr
ledger.write_bytes(lr + append.encode())
assert ip.read_bytes() == ir
ip.write_text(json.dumps(intake, indent=2) + '\n')
out = {'observed_utc': now, 'correctness': gate, 'contribution': 'PENDING',
       'count': 19, 'modified_task_indices': [687, 689], 'old_task_count': len(old['tasks']),
       'all_other_task_entries_unchanged': True, 'active_indices': active}
(P / 'integration-record.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
