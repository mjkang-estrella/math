"""Bounded integration of the notified Arithmetic161 result and new dispatch."""
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
before, journal = T.read_bytes(), J.read_bytes()
assert sha(before) == base['tasks_sha256'] and sha(journal) == base['journal_sha256']
old = json.loads(before)
assert len(old['tasks']) == base['tasks'] == 651
assert (old['newAccepted'], old['target'], old['remaining'], old['latestAcceptance']) == (19, 20, 1, 'R041')
intake = json.loads((O / 'intake.json').read_bytes())
terminal = json.loads((O / 'task-status.json').read_bytes())['structuredContent']
dispatch = json.loads((O / 'arithmetic-r162-dispatch.json').read_bytes())['structuredContent']
request = json.loads((O / 'private/submitted-prompt.json').read_bytes())
iso = json.loads((O / 'prospective-isolation-arithmetic162.json').read_bytes())
assert terminal['taskId'] == old['tasks'][649]['taskId'] and terminal['status'] == 'completed'
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
assert b'*t185144-*' in brief and b'*k369134-*' in brief
for peer in iso['existing_peer_original_initial_briefs']:
    data = (P / peer['brief']).read_bytes()
    assert sha(data) == peer['sha256'] and b'*arithmetic*r162*' in data
for path, expected in base['protected_unrelated_sha256'].items():
    assert sha((P / path).read_bytes()) == expected
assert not subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=P)
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
new = copy.deepcopy(old)
new['tasks'][649].update(terminal)
new['tasks'][649].update({'parent_full_intake_pending': False, 'parent_disposition': intake['status'], 'parent_intake': str((O / 'intake.json').relative_to(B)), 'parent_assessment_sha256': intake['assessment_sha256'], 'parent_intake_utc': now, 'status_provenance': 'Actual single notified terminal task_status response, archived raw.', 'accepted': False, 'count_change': 0})
task = copy.deepcopy(dispatch)
task.update({'observed_utc': now, 'target': request['target'], 'role': request['role'], 'title': request['title'], 'output': 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162/', 'brief': iso['new_brief']['path'], 'brief_sha256': iso['new_brief']['sha256'], 'brief_bytes': iso['new_brief']['bytes'], 'source_family_navigation': 'Source064; exact catalogue [109955,111051), one pinned mu-constant surface-singularity folder with24 descendants /21 blobs. Metadata navigation only; actual proofs assigned reading.', 'parent_count_at_dispatch': 19, 'accepted': False, 'count_change': 0, 'publication': 'STOPPED', 'dispatch_receipt': str((O / 'arithmetic-r162-dispatch.json').relative_to(B)), 'prospective_isolation': str((O / 'prospective-isolation-arithmetic162.json').relative_to(B)), 'clientRequestId': request['clientRequestId'], 'round': 1, 'parent_thread': '6742db91-d35c-44d0-a762-e5d9232f5177', 'status_provenance': 'Actual successful delegate_task response; running at dispatch, not a later liveness poll.'})
new['tasks'].append(task)
foreign_task = old['tasks'][650]
foreign = [{'task_index': 650, 'taskId': foreign_task['taskId'], 'parent_thread': foreign_task['parent_thread'], 'shared_record_status': foreign_task['status'], 'current_thread_status_request': 'not_requested_foreign_owner', 'current_liveness_verified_here': False, 'action': 'Preserved; no query, body/activity inspection, steering or duplicate replacement.'}]
note = 'Arithmetic161 (idx649, Source063) completed PREFREEZE/no nominee and archived: eliminating the divisor-supported all-minimal quantum word for full defect-two low-degree chain connectivity remains unpaid. Exact69-file packet verification and finite checks passed; no grade/count. Late special no-r alias installation disclosed. Arithmetic162 (idx651, Source064 mu-constant surface singularities) dispatched with Astra high/default and explicit prospective special aliases. Foreign-owned Structural193 (idx650) and prior owner archives preserved. Campaign19/20, latestR041, one remains; publication STOPPED.'
new['last_parent_progress'] = note
s = new['current_work_snapshot']
s.update({'observed_utc': now, 'note': note, 't3_current_confirmed_running': [dispatch['taskId']], 'fresh_discovery_current': [task['output']], 't3_recorded_running_different_owner': foreign, 't3_last_polled_running_note': 'Historical foreign-owner list retained. Current own confirmed list is based on Arithmetic162 dispatch; Structural193 liveness is not freshly verified here.', 'arithmetic_r161_archive': {'task_index': 649, 'status': intake['status'], 'intake': str((O / 'intake.json').relative_to(B)), 'accepted': False, 'count_change': 0}})
s['t3_dispatch_observations'].append({'observed_utc': now, **copy.deepcopy(dispatch)})
changes = {'baseline': base['head'], 'old_tasks': 651, 'new_tasks': 652, 'changed_old_task_indices': [i for i in range(651) if old['tasks'][i] != new['tasks'][i]], 'changed_snapshot_keys': sorted(k for k in set(old['current_work_snapshot']) | set(s) if old['current_work_snapshot'].get(k) != s.get(k)), 'count_change': 0, 'newAccepted': 19, 'remaining': 1, 'foreign_task_record_unchanged': old['tasks'][650] == new['tasks'][650]}
assert changes['changed_old_task_indices'] == [649]
dump(O / 'integration-changes.json', changes)
appendix = ('\n\n### 2026-10-22: Arithmetic161 no-nominee archive; Arithmetic162 dispatch\n\n' + note + '\n\n'
    + 'The full exploratory scope includes every pair on every smooth complex projective Fano with i>=3 and n=r(i-1)+2. All full families of degree<=i+2 enter the saturated quotient. Failure reduces to a nonzero divisor-supported all-minimal quantum word; the Fano blow-up stress test and smooth common-divisor adjunction calculation do not eliminate the actual singular/intermediate support. No theorem was frozen or independently graded. All10 canonical blobs and two original full-file extents matched; author source/primary semantic-reading extents and limitations remain author records, not a fresh parent proof review. The entire85-file root was unchanged.\n\n'
    + 'Special no-r aliases t185144 and k369134 were installed late in161, with no rerun; this chronology is not retrospectively repaired. The162 initial brief explicitly installs both before traversal/body selection. The foreign Structural193 initial brief already excluded162 before root/brief creation; no live peer findings or activity were inspected. Prior foreign archives remain untouched. The new Source064 one-parameter right-triviality headline is paid; actual operative source reading and a distinct full-scope construction are assigned to162. All protected private bodies and named metadata remain unstaged. See discovery-arithmetic-r161-parent/assessment.md and intake.json.\n')
(O / 'private/journal-append.bin').write_bytes(appendix.encode())
assert T.read_bytes() == before and J.read_bytes() == journal
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=P, text=True).strip() == base['head']
dump(T, new)
J.write_bytes(journal + appendix.encode())
print(json.dumps(changes))
