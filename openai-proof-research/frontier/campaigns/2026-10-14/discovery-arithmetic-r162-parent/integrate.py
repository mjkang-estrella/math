"""Bounded notified-result intake and distinct covered-namespace dispatch."""
from pathlib import Path
import copy
import datetime
import fnmatch
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
before, journal = T.read_bytes(), J.read_bytes()
assert sha(before) == base['tasks_sha256'] and sha(journal) == base['journal_sha256']
old = json.loads(before)
assert len(old['tasks']) == base['tasks'] == 653
assert (old['newAccepted'], old['target'], old['remaining'], old['latestAcceptance']) == (19, 20, 1, 'R041')
intake = json.loads((O / 'intake.json').read_bytes())
terminal = json.loads((O / 'task-status.json').read_bytes())['structuredContent']
dispatch = json.loads((O / 'arithmetic-r162b-dispatch.json').read_bytes())['structuredContent']
request = json.loads((O / 'private/submitted-prompt.json').read_bytes())
iso = json.loads((O / 'prospective-isolation-arithmetic162b.json').read_bytes())
assert terminal['taskId'] == old['tasks'][651]['taskId'] and terminal['status'] == 'completed'
assert dispatch['status'] == 'running' and dispatch['workState'] == 'working'
assert all(x.get('taskId') != dispatch['taskId'] for x in old['tasks'])
for r in [terminal, dispatch]:
    assert not r['hasPendingChildRuns'] and not r['hasPendingQuestion'] and r['pendingApproval'] is None
    assert (r['providerInstanceId'], r['model']) == ('codex', 'gpt-6-astra')
    assert {x['id']: x['value'] for x in r['options']} == {'reasoningEffort': 'high', 'serviceTier': 'default'}
assert intake['status'] == 'PREFREEZE_NO_NOMINEE_ARCHIVED' and not intake['accepted'] and intake['count_change'] == 0
assert sha((O / 'assessment.md').read_bytes()) == intake['assessment_sha256']
brief = (P / iso['new_brief']['path']).read_bytes()
assert brief.decode() == request['task'] and sha(brief) == iso['new_brief']['sha256']
for peer in iso['existing_peer_original_initial_briefs']:
    data = (P / peer['brief']).read_bytes()
    assert sha(data) == peer['sha256'] and b'*arithmetic*r162*' in data
assert fnmatch.fnmatchcase('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162b/packet/FINAL.md'.casefold(), '*arithmetic*r162*')
assert b'*t185144-*' in brief and b'*k369134-*' in brief
for path, expected in base['protected_unrelated_sha256'].items():
    assert sha((P / path).read_bytes()) == expected
assert not subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=P)
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
new = copy.deepcopy(old)
new['tasks'][651].update(terminal)
new['tasks'][651].update({'parent_full_intake_pending': False, 'parent_disposition': intake['status'], 'parent_intake': str((O / 'intake.json').relative_to(B)), 'parent_assessment_sha256': intake['assessment_sha256'], 'parent_intake_utc': now, 'status_provenance': 'Actual single notified terminal task_status response, archived raw.', 'accepted': False, 'count_change': 0})
task = copy.deepcopy(dispatch)
task.update({'observed_utc': now, 'target': request['target'], 'role': request['role'], 'title': request['title'], 'output': 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162b/', 'brief': iso['new_brief']['path'], 'brief_sha256': iso['new_brief']['sha256'], 'brief_bytes': iso['new_brief']['bytes'], 'source_family_navigation': 'Source065; exact catalogue [111051,112793), two pinned Virasoro folders with31 descendants /26 blobs. Metadata navigation only; actual proofs assigned reading.', 'round_namespace': 'Arithmetic162b is a NEW DISTINCT family, covered by the peer original *arithmetic*r162* guard; no retry of162 mu-constant scope.', 'parent_count_at_dispatch': 19, 'accepted': False, 'count_change': 0, 'publication': 'STOPPED', 'dispatch_receipt': str((O / 'arithmetic-r162b-dispatch.json').relative_to(B)), 'prospective_isolation': str((O / 'prospective-isolation-arithmetic162b.json').relative_to(B)), 'clientRequestId': request['clientRequestId'], 'round': 1, 'parent_thread': '6742db91-d35c-44d0-a762-e5d9232f5177', 'status_provenance': 'Actual successful delegate_task response; running at dispatch, not a later liveness poll.'})
new['tasks'].append(task)
note = 'Arithmetic162 (idx651, Source064) completed PREFREEZE/no nominee and archived: full ambient joint bi-Holder completion across nonzero Milnor levels with bilateral two-point bounds remains unpaid. Exact67-file verification passed; all21 canonical blobs and two original spans matched; no grade/count. Arithmetic162b (idx653, DISTINCT Source065 full ordinary Virasoro family, both companions) dispatched with Astra high/default inside the original arithmetic162 namespace exclusion. Coordination rebased onto the owner archive of Structural193 and dispatch of Structural194 (idx652), both preserved. No peer query/inspection/steering; no163 root/brief created. Campaign19/20, latestR041, one remains; publication STOPPED.'
new['last_parent_progress'] = note
s = new['current_work_snapshot']
s.update({'observed_utc': now, 'note': note, 't3_current_confirmed_running': [dispatch['taskId']], 'fresh_discovery_current': [task['output']], 't3_last_polled_running_note': 'Historical foreign-owner list retained. Current own confirmed list is based on Arithmetic162b dispatch; Structural194 liveness is not freshly verified here.', 'arithmetic_r162_archive': {'task_index': 651, 'status': intake['status'], 'intake': str((O / 'intake.json').relative_to(B)), 'accepted': False, 'count_change': 0}})
s['t3_recorded_running_different_owner'] = [{'task_index': 652, 'taskId': old['tasks'][652]['taskId'], 'parent_thread': old['tasks'][652]['parent_thread'], 'shared_record_status': old['tasks'][652]['status'], 'current_thread_status_request': 'not_requested_foreign_owner', 'current_liveness_verified_here': False, 'action': 'Preserved without status query, body/activity inspection, steering or duplicate dispatch.'}]
s['t3_dispatch_observations'].append({'observed_utc': now, **copy.deepcopy(dispatch)})
changes = {'baseline': base['head'], 'old_tasks': 653, 'new_tasks': 654, 'changed_old_task_indices': [i for i in range(653) if old['tasks'][i] != new['tasks'][i]], 'changed_snapshot_keys': sorted(k for k in set(old['current_work_snapshot']) | set(s) if old['current_work_snapshot'].get(k) != s.get(k)), 'count_change': 0, 'newAccepted': 19, 'remaining': 1, 'foreign_task_record_unchanged': old['tasks'][652] == new['tasks'][652], 'owner_archive_unchanged': old['tasks'][650] == new['tasks'][650]}
assert changes['changed_old_task_indices'] == [651]
dump(O / 'integration-changes.json', changes)
appendix = ('\n\n### 2026-10-22: Arithmetic162 archive; distinct Arithmetic162b Virasoro discovery\n\n' + note + '\n\n'
    + 'The unchanged quantitative target retains every family, all spatial/parameter pairs and both directions. Finite jets, analytic equal-fiber control, the exact zero-family seam, finite-length collapse/attaching data and a power-sized normal-neighborhood construction remain retained. Full ambient bilateral two-point control, including low cases, is not proved. The constant xy+z2 example refutes an arbitrary-field-to-flow inference, not the existential theorem. No theorem frozen, independent grade or count. All six authored notes and exact reading/isolation limits were read; source/primary semantic extents remain author records, not a fresh parent proof review. The82-file root remained unchanged.\n\n'
    + 'The next family is065, both Virasoro canonical companions. The proposed163 literal-guard check failed before creation. Arithmetic162b is a new independent round within the already prospectively excluded arithmetic162 namespace, not a continuation or restriction of the mu-constant question. No peer query, body/activity inspection or steering occurred. Actual source065 proof reading is assigned. All protected private bodies and named metadata remain unstaged. See discovery-arithmetic-r162-parent/assessment.md and intake.json.\n')
(O / 'private/journal-append.bin').write_bytes(appendix.encode())
assert T.read_bytes() == before and J.read_bytes() == journal
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=P, text=True).strip() == base['head']
dump(T, new)
J.write_bytes(journal + appendix.encode())
print(json.dumps(changes))
