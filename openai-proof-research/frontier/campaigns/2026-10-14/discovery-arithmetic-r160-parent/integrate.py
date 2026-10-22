"""Integrate the completed Arithmetic160 intake and actual Arithmetic161 dispatch."""
from pathlib import Path
import copy
import datetime
import hashlib
import json
import subprocess

P = Path(__file__).resolve().parents[4]
B = P / 'frontier/campaigns/2026-10-14'
O = Path(__file__).resolve().parent
T = B / 'tasks.json'
J = P / 'frontier/NEW-TEN-2026-10-14.md'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')

base = json.loads((O / 'integration-baseline.json').read_bytes())
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=P, text=True).strip() == base['head']
before = T.read_bytes()
journal = J.read_bytes()
assert sha(before) == base['tasks_sha256'] and sha(journal) == base['journal_sha256']
assert len(journal) == base['journal_bytes']
old = json.loads(before)
assert len(old['tasks']) == 649
assert (old['newAccepted'], old['remaining'], old['latestAcceptance']) == (19, 1, 'R041')
intake = json.loads((O / 'intake.json').read_bytes())
terminal = json.loads((O / 'task-status.json').read_bytes())['structuredContent']
dispatch = json.loads((O / 'arithmetic-r161-dispatch.json').read_bytes())['structuredContent']
request = json.loads((O / 'private/submitted-prompt.json').read_bytes())
assert terminal['taskId'] == old['tasks'][648]['taskId'] and terminal['status'] == 'completed'
for result in [terminal, dispatch]:
    assert not result['hasPendingChildRuns'] and not result['hasPendingQuestion'] and result['pendingApproval'] is None
    assert (result['providerInstanceId'], result['model']) == ('codex', 'gpt-6-astra')
    assert {x['id']: x['value'] for x in result['options']} == {'reasoningEffort': 'high', 'serviceTier': 'default'}
assert dispatch['status'] == 'running' and dispatch['workState'] == 'working'
assert all(x.get('taskId') != dispatch['taskId'] for x in old['tasks'])
assert intake['status'] == 'PREFREEZE_NO_NOMINEE_ARCHIVED' and not intake['accepted'] and intake['count_change'] == 0
assert sha((O / 'assessment.md').read_bytes()) == intake['assessment_sha256']
iso = json.loads((O / 'prospective-isolation-arithmetic161.json').read_bytes())
brief = (P / iso['new_brief']['path']).read_bytes()
assert brief.decode() == request['task'] and sha(brief) == iso['new_brief']['sha256']
marker = b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
assert len(brief.split(marker, 1)[1]) == 5570
for peer in iso['existing_peer_original_initial_briefs']:
    data = (P / peer['brief']).read_bytes()
    assert sha(data) == peer['sha256'] and b'*arithmetic*r161*' in data
for path, expected in base['protected_unrelated_sha256'].items():
    assert sha((P / path).read_bytes()) == expected
assert not subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=P)
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
new = copy.deepcopy(old)
new['tasks'][648].update(terminal)
new['tasks'][648].update({
    'parent_full_intake_pending': False,
    'parent_disposition': intake['status'],
    'parent_intake': str((O / 'intake.json').relative_to(B)),
    'parent_assessment_sha256': intake['assessment_sha256'],
    'parent_intake_utc': now,
    'status_provenance': 'Single actual notified terminal task_status response; structured fields transcribed in the parent receipt.',
    'accepted': False, 'count_change': 0
})
task = copy.deepcopy(dispatch)
task.update({
    'observed_utc': now, 'target': request['target'], 'role': request['role'], 'title': request['title'],
    'output': 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r161/',
    'brief': iso['new_brief']['path'], 'brief_sha256': iso['new_brief']['sha256'], 'brief_bytes': iso['new_brief']['bytes'],
    'source_family_navigation': 'Source063 generalized Mukai; one exact catalogue body [109073,109955), one pinned folder with 12 descendants / 10 blobs. Metadata navigation only; no parent source-proof reading claimed.',
    'parent_count_at_dispatch': 19, 'accepted': False, 'count_change': 0, 'publication': 'STOPPED',
    'dispatch_receipt': str((O / 'arithmetic-r161-dispatch.json').relative_to(B)),
    'prospective_isolation': str((O / 'prospective-isolation-arithmetic161.json').relative_to(B)),
    'clientRequestId': request['clientRequestId'], 'round': 1,
    'parent_thread': '6742db91-d35c-44d0-a762-e5d9232f5177',
    'status_provenance': 'Actual successful delegate_task response; running at dispatch, not a later liveness poll.'
})
new['tasks'].append(task)
note = 'Arithmetic160 (idx648, Source062) completed PREFREEZE/no nominee and archived: full global contact tensor with correct all-sheet jets and boundary compatibility remains unpaid. Packet and finite controls replayed; no mathematical grade/count. Arithmetic161 (idx649, Source063 generalized Mukai) dispatched with Astra high/default. Foreign-owned Arithmetic159/Structural192 records preserved without new liveness claims or body inspection. Campaign 19/20, latest R041, one remains; publication STOPPED.'
new['last_parent_progress'] = note
s = new['current_work_snapshot']
s.update({
    'observed_utc': now, 'note': note,
    't3_current_confirmed_running': [dispatch['taskId']],
    'fresh_discovery_current': [task['output']],
    't3_last_polled_running_note': 'Retained historical foreign-owner list; current own confirmed list is based on Arithmetic161 dispatch. No foreign status requery or liveness verification.',
    'arithmetic_r160_archive': {'task_index': 648, 'status': intake['status'], 'intake': str((O / 'intake.json').relative_to(B)), 'accepted': False, 'count_change': 0}
})
s['t3_dispatch_observations'].append({'observed_utc': now, **copy.deepcopy(dispatch)})
changes = {
    'baseline': base['head'], 'old_tasks': 649, 'new_tasks': 650,
    'changed_old_task_indices': [i for i in range(649) if old['tasks'][i] != new['tasks'][i]],
    'changed_snapshot_keys': sorted(k for k in set(old['current_work_snapshot']) | set(s) if old['current_work_snapshot'].get(k) != s.get(k)),
    'count_change': 0, 'newAccepted': 19, 'remaining': 1,
    'foreign_task_records_unchanged': old['tasks'][646:648] == new['tasks'][646:648]
}
assert changes['changed_old_task_indices'] == [648]
dump(O / 'integration-changes.json', changes)
appendix = ('\n\n### 2026-10-22: Arithmetic160 no-nominee archive; Arithmetic161 dispatch\n\n' + note + '\n\n'
    + 'The retained contact construction includes a proper dominating family, fixed-end higher-degree control, scalar/vector boundary valuations, additive thickness, and normalized trace. Uniform scalar extension and correct diagonal jets on every sheet remain unproved; local compatibility tests are not global counterexamples. No frozen statement, correctness/contribution grade, or acceptance is assigned. The parent read the complete authored derivations, recovered a clipped note02 display, replayed the finite arithmetic and exact 67-file packet verification, and preserved the 76-file root. All14 canonical blobs and three original spans matched; actual source/primary semantic reading extents remain the author recorded claims, not a new parent proof review.\n\n'
    + 'Arithmetic161 selects only Source063 and one exact pinned folder. Both foreign peers initial briefs excluded its namespace before root/brief creation; neither peer was queried, inspected or steered this turn. Source063 actual operative proofs remain assigned reading. Private source/primary/history/navigation material and named metadata remain unstaged. See discovery-arithmetic-r160-parent/assessment.md and intake.json for the exact scope, limits and detached anchors.\n')
(O / 'private/journal-append.bin').write_bytes(appendix.encode())
assert T.read_bytes() == before and J.read_bytes() == journal
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=P, text=True).strip() == base['head']
dump(T, new)
J.write_bytes(journal + appendix.encode())
print(json.dumps(changes))
