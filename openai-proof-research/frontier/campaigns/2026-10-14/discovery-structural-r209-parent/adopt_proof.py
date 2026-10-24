#!/usr/bin/env python3
"""Adopt only the delivered full-scope correctness review; preserve other work."""
from pathlib import Path
import copy, datetime, hashlib, json, os

P = Path(__file__).resolve().parent
C = P.parent
PROJECT = C.parents[2]
read = lambda p: json.loads(p.read_bytes())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
d = read(P / 'proof-task-status.json')
r = read(P / 'proof-replay.json')
owner = '164b1204-be68-4540-94bb-0b91055c4381'
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
assert d['status'] == 'completed' and not d['hasPendingChildRuns']
assert d['providerInstanceId'] == 'codex' and d['model'] == 'gpt-6-astra'
assert {e['id']: e['value'] for e in d['options']} == {'reasoningEffort': 'xhigh', 'serviceTier': 'default'}
assert r['review_originals_unchanged'] and r['author_files_unchanged'] == 85
assert r['verification']['artifact_verification'] == r['author_verification']['artifact_verification'] == 'PASS'
registry = C / 'tasks.json'
ledger = PROJECT / 'frontier/NEW-TEN-2026-10-14.md'
raw = registry.read_bytes()
lr = ledger.read_bytes()
t = json.loads(raw)
old = copy.deepcopy(t)
assert (t['newAccepted'], t['latestAcceptance'], t['remaining']) == (19, 'R041', 1)
author = t['tasks'][721]
review = t['tasks'][723]
assert author['parent_thread'] == review['parent_thread'] == owner
assert author['correctness'] == author['contribution'] == 'PENDING'
assert review['taskId'] == d['taskId'] and review['parent_full_intake_pending']
assert sha(PROJECT / review['brief']) == review['brief_sha256'] == 'd7275e2be308c629177822ff65ce01baa9d22cb8f29da50a9c9844f6e43faf99'
intake_path = P / 'intake.json'
ir = intake_path.read_bytes()
intake = json.loads(ir)
old_intake = copy.deepcopy(intake)
disposition = 'CORRECTNESS_PASS_CONTRIBUTION_PENDING'
proof_intake = {
    'observed_utc': now, 'parent_thread': owner, 'task_index': 723,
    'taskId': d['taskId'], 'author_task_index': 721, 'source_index': 333,
    'correctness': 'PASS', 'scope': 'Entire unchanged frozen statement and submitted proof',
    'upstream_truth_stipulated': True, 'essential_repairs': [], 'unresolved_correctness_obligations': [],
    'contribution': 'PENDING', 'accepted': False, 'count_change': 0,
    'newAccepted': 19, 'latestAcceptance': 'R041', 'remaining': 1, 'publication': 'STOPPED',
    'frozen_sha256': author['frozen_sha256'], 'proof_sha256': author['proof_sha256'],
    'assessment_sha256': sha(P / 'proof-assessment.md'), 'anchors': r['anchors'], 'artifact_replay': r,
    'next': 'Await the already dispatched independent contribution result; no liveness polling or new review round.'
}
for k in ['status', 'workState', 'hasPendingChildRuns', 'latestTerminalRunId', 'latestTerminalStatus', 'latestTerminalSummary', 'latestTerminalResultContextTransferId', 'summary', 'resultContextTransferId', 'hasPendingQuestion', 'pendingApproval', 'waitTimedOut', 'observed_utc']:
    review[k] = d[k]
review.update(parent_full_intake_pending=False, parent_disposition='FULL_SCOPE_CORRECTNESS_PASS', correctness='PASS', parent_intake='discovery-structural-r209-parent/proof-intake.json', parent_intake_utc=now, accepted=False, count_change=0, status_provenance='Terminal lookup after delivered owned completion; no contribution or foreign liveness lookup.')
author.update(correctness='PASS', parent_disposition=disposition, correctness_intake='discovery-structural-r209-parent/proof-intake.json')
intake.update(correctness='PASS', disposition=disposition, correctness_intake='discovery-structural-r209-parent/proof-intake.json', correctness_adopted_utc=now, next=proof_intake['next'])
s = t['current_work_snapshot']
for rows in [author['review_dispatches'], intake['review_dispatches'], s['structural209_review_dispatches']]:
    own = [x for x in rows if x['task_index'] == 723]
    assert len(own) == 1 and own[0]['taskId'] == d['taskId']
    own[0].update(status='completed', correctness='PASS', intake='discovery-structural-r209-parent/proof-intake.json')
for key in ['structural209_dispatch', 'structural209_parent_intake']:
    s[key].update(disposition=disposition, correctness='PASS', contribution='PENDING')
s['structural209_correctness_adoption'] = {'task_index': 723, 'correctness': 'PASS', 'contribution': 'PENDING', 'scope': proof_intake['scope'], 'intake': 'discovery-structural-r209-parent/proof-intake.json', 'count_change': 0}
if 'active_task_indices' in s:
    s['active_task_indices'] = [i for i in s['active_task_indices'] if i != 723]
if 't3_last_polled_running' in s:
    s['t3_last_polled_running'] = [x for x in s['t3_last_polled_running'] if x != d['taskId']]
note = 'Structural209 full-scope correctness PASS adopted under stipulated upstream truth. Independent contribution remains PENDING. No acceptance or count. Campaign 19/20, latest R041, one remaining; publication STOPPED. Other task records preserved.'
t['last_parent_progress'] = note
s.update(observed_utc=now, note=note)
changed = [i for i, x in enumerate(old['tasks']) if t['tasks'][i] != x]
assert changed == [721, 723] and len(t['tasks']) == len(old['tasks'])
assert all(t[k] == old[k] for k in old if k not in ['tasks', 'current_work_snapshot', 'last_parent_progress'])
allowed = {'observed_utc', 'note', 'active_task_indices', 't3_last_polled_running', 'structural209_dispatch', 'structural209_parent_intake', 'structural209_review_dispatches'}
assert all(s[k] == v for k, v in old['current_work_snapshot'].items() if k not in allowed)
for before, after in [(old['tasks'][721]['review_dispatches'], author['review_dispatches']), (old_intake['review_dispatches'], intake['review_dispatches']), (old['current_work_snapshot']['structural209_review_dispatches'], s['structural209_review_dispatches'])]:
    assert [x for x in before if x['task_index'] != 723] == [x for x in after if x['task_index'] != 723]
assert author['contribution'] == intake['contribution'] == 'PENDING'
heading = '## Structural209 correctness adoption: full unchanged scope PASS'
assert heading.encode() not in lr
append = '\n' + heading + '\n\nThe parent read the complete independent [correctness review](campaigns/2026-10-14/structural-r209-proof-r1/REVIEW.md) and adopts **PASS** for the entire unchanged frozen statement and submitted proof T333Q209, relative to stipulated upstream truth. No essential repair or unresolved correctness obligation remains. The review covers the two-sign periodic obstruction calculation, finite derivative budget, uniform initial threshold with higher norms affecting only subsequent waiting times, smooth convergence, global embedding and sharp lower bound. See the [parent assessment](campaigns/2026-10-14/discovery-structural-r209-parent/proof-assessment.md).\n\nRead-only replay matched all 21 selected review files, three outside files and three directories. All 85 author files and observed modes remained unchanged; seven tiny parent-local copied controls behaved as expected. Source and primary identities, reading extents and renders were bound without claiming inherited semantic reading or visual inspection. The comparator supplies no proved endpoint coverage.\n\nThe independent contribution decision remains **PENDING** and has not been polled or inspected in this intake. No acceptance or count. **19/20, latest R041, one remaining; publication STOPPED.**\n'
assert registry.read_bytes() == raw and ledger.read_bytes() == lr and intake_path.read_bytes() == ir
(P / 'proof-intake.json').write_text(json.dumps(proof_intake, indent=2) + '\n')
intake_path.write_text(json.dumps(intake, indent=2) + '\n')
tmp = registry.with_suffix('.structural209-proof.tmp')
tmp.write_text(json.dumps(t, indent=2) + '\n')
assert registry.read_bytes() == raw
os.replace(tmp, registry)
assert ledger.read_bytes() == lr
ledger.write_bytes(lr + append.encode())
record = {'observed_utc': now, 'changed_existing_tasks': changed, 'new_tasks': 0, 'all_other_tasks_unchanged': True, 'other_snapshot_entries_preserved': True, 'contribution_task_and_dispatch_unchanged': True, 'correctness': 'PASS', 'contribution': 'PENDING', 'count_change': 0}
(P / 'proof-adoption-record.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
