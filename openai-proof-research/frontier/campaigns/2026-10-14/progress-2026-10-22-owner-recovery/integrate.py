"""Integrate only this parent's verified dispatch and coordination corrections."""
from pathlib import Path
import copy
import datetime
import hashlib
import json
import subprocess

P = Path(__file__).resolve().parents[4]
B = P / 'frontier/campaigns/2026-10-14'
O = Path(__file__).resolve().parent
TP = B / 'tasks.json'
JP = P / 'frontier/NEW-TEN-2026-10-14.md'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')

base = json.loads((O / 'integration-baseline.json').read_bytes())
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=P, text=True).strip() == base['head']
old_bytes = TP.read_bytes()
old_journal = JP.read_bytes()
assert sha(old_bytes) == base['tasks_sha256']
assert sha(old_journal) == base['journal_sha256']
assert len(old_journal) == base['journal_bytes']
old = json.loads(old_bytes)
assert len(old['tasks']) == base['tasks'] == 648
assert (old['newAccepted'], old['target'], old['remaining'], old['latestAcceptance']) == (19, 20, 1, 'R041')
for path, expected in base['protected_unrelated_sha256'].items():
    assert sha((P / path).read_bytes()) == expected
assert not subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=P)

request = json.loads((O / 'private/submitted-prompt.json').read_bytes())
raw = json.loads((O / 'arithmetic-r160-dispatch.json').read_bytes())
r = raw['structuredContent']
assert not raw.get('isError')
assert (r['status'], r['workState'], r['providerInstanceId'], r['model']) == ('running', 'working', 'codex', 'gpt-6-astra')
assert {x['id']: x['value'] for x in r['options']} == request['target']['options'] == {'reasoningEffort': 'high', 'serviceTier': 'default'}
assert not r['hasPendingChildRuns'] and not r['hasPendingQuestion'] and r['pendingApproval'] is None
assert all(t.get('taskId') != r['taskId'] for t in old['tasks'])
iso = json.loads((O / 'prospective-isolation.json').read_bytes())
brief = P / iso['new_brief']['path']
assert brief.read_text() == request['task']
assert sha(brief.read_bytes()) == iso['new_brief']['sha256']
assert len(brief.read_bytes()) == iso['new_brief']['bytes']
marker = b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
suffix = brief.read_bytes().split(marker, 1)[1]
assert len(suffix) == 5570
for peer in iso['existing_peer_original_initial_briefs']:
    initial = (P / peer['brief']).read_bytes()
    assert sha(initial) == peer['sha256']
    assert b'*arithmetic*r160*' in initial
    assert suffix == initial.split(marker, 1)[1]
assert b'*arithmetic*r159*' in brief.read_bytes()
assert b'*structural*r192*' in brief.read_bytes()
for i in (625, 627, 630, 631):
    assert old['tasks'][i]['parent_disposition'] == 'PREFREEZE_NO_NOMINEE_ARCHIVED'
    assert not old['tasks'][i]['accepted'] and old['tasks'][i]['count_change'] == 0
assert old['tasks'][637]['parent_disposition'] == 'FULL_SCOPE_PASS_TECHNICAL_CLOSED'

now = datetime.datetime.now(datetime.timezone.utc).isoformat()
foreign = [{
    'task_index': i,
    'taskId': old['tasks'][i]['taskId'],
    'parent_thread': old['tasks'][i]['parent_thread'],
    'shared_record_status': old['tasks'][i]['status'],
    'current_thread_status_request': 'task_not_found_different_owner',
    'current_liveness_verified_here': False,
    'action': 'Preserved; no cancellation, duplicate dispatch, requery or live-body/activity bypass.'
} for i in (646, 647)]
record = {
    'observed_utc': now,
    'user_instruction': 'Keep progress',
    'parent_thread': '6742db91-d35c-44d0-a762-e5d9232f5177',
    'baseline_commit': base['head'],
    'reconciliation': {
        'archived_intakes': [625, 627],
        'interrupted_tasks': [628, 629],
        'completed_recovery_tasks': [630, 631],
        'arithmetic156': 'Full-scope PASS / TECHNICAL closed; zero count; no desired-grade retry or downstream work.',
        'pause_revoked_by_latest_user_resume': True,
        'historical_pause_and_resume_receipts_preserved': True
    },
    'foreign_recorded_running': foreign,
    'new_dispatch': {'task_index': 648, 'taskId': r['taskId'], 'receipt': str((O / 'arithmetic-r160-dispatch.json').relative_to(B)), 'status_provenance': 'Actual successful delegate_task response; running at dispatch, not a subsequent liveness poll.'},
    'isolation': 'prospective-isolation.json',
    'new_source_navigation': {'family': 62, 'folders': 1, 'entries': 17, 'blobs': 14, 'parent_read_actual_proofs': False},
    'reading_limits': [
        'No live Arithmetic159 or Structural192 body, findings or activity was inspected. Initial briefs and shared coordination metadata only.',
        'A coordination-output call accidentally printed the full historical current_work_snapshot and was truncated; no complete semantic read is claimed. Subsequent reads selected only required keys.',
        'Two overbroad filename-only administrative searches listed AGENTS.md paths and tracked journal-named paths, including unrelated protected metadata names. No listed source/primary/history body was opened through those searches. This is a navigation/isolation lapse, not a perfect-isolation claim.',
        'Exact Source062 catalogue-body and tree metadata selection is navigation only. Actual operative source and primary proof reading is assigned to Arithmetic160.',
        'All source, primary, history, search and copied-body materials and private navigation/status-error records remain unstaged.'
    ],
    'newAccepted': 19, 'target': 20, 'remaining': 1, 'latestAcceptance': 'R041',
    'accepted': False, 'count_change': 0, 'publication': 'STOPPED'
}
task = copy.deepcopy(r)
task.update({
    'observed_utc': now, 'target': request['target'], 'role': request['role'], 'title': request['title'],
    'output': 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r160/',
    'brief': iso['new_brief']['path'], 'brief_sha256': iso['new_brief']['sha256'], 'brief_bytes': iso['new_brief']['bytes'],
    'source_family_navigation': 'Source062; one pinned contact-Fano/LeBrun-Salamon folder, 17 entries / 14 blobs. Metadata navigation only; no parent source-proof reading claimed.',
    'parent_count_at_dispatch': 19, 'accepted': False, 'count_change': 0, 'publication': 'STOPPED',
    'dispatch_receipt': str((O / 'arithmetic-r160-dispatch.json').relative_to(B)),
    'prospective_isolation': str((O / 'prospective-isolation.json').relative_to(B)),
    'clientRequestId': request['clientRequestId'], 'round': 1, 'parent_thread': record['parent_thread'],
    'status_provenance': record['new_dispatch']['status_provenance']
})
new = copy.deepcopy(old)
new['tasks'].append(task)
note = 'Arithmetic160 (idx648, Source062 contact-Fano/LeBrun-Salamon) dispatched with Astra high/default. Arithmetic159 (idx646) and Structural192 (idx647) remain recorded-running under another owner; this parent cannot certify their current liveness and did not inspect or replace them. Stale pause/intake flags reconciled against completed archives/recoveries; Arithmetic156 PASS/TECHNICAL closure preserved. Campaign 19/20, latest R041, one remains; publication STOPPED.'
new['last_parent_progress'] = note
s = new['current_work_snapshot']
s.update({'observed_utc': now, 'note': note, 'user_pause_requested': False,
          'paused_unfinished_task_indices': [], 'pending_terminal_intakes_20261021': [],
          'user_resume_requested': True,
          'latest_resume_reconciliation': str((O / 'reconciliation.json').relative_to(B)),
          't3_current_confirmed_running': [r['taskId']],
          't3_recorded_running_different_owner': foreign,
          'fresh_discovery_current': [task['output']],
          't3_last_polled_running_note': 'Retained historical list from the other parent. Current confirmed list is based on this parent actual Arithmetic160 dispatch; foreign ownership errors do not verify liveness.'})
s['t3_dispatch_observations'].append({'observed_utc': now, **copy.deepcopy(r)})
changed_snapshot_keys = sorted(k for k in set(old['current_work_snapshot']) | set(s) if old['current_work_snapshot'].get(k) != s.get(k))
record['changed_snapshot_keys'] = changed_snapshot_keys
assert new['tasks'][:648] == old['tasks']
assert {k: v for k, v in new.items() if k not in ('tasks', 'last_parent_progress', 'current_work_snapshot')} == {k: v for k, v in old.items() if k not in ('tasks', 'last_parent_progress', 'current_work_snapshot')}
dump(O / 'reconciliation.json', record)
appendix = ('\n\n### 2026-10-22: resume coordination and distinct Arithmetic160 dispatch\n\n'
            + note + '\n\n'
            + 'The latest user instruction, "Keep progress", resumes this parent. Existing completed intake/recovery and PASS/TECHNICAL decisions are preserved with zero new count. One ownership-limited status request per foreign task returned task_not_found; those errors are not terminal results. Both original peer briefs excluded Arithmetic160 before its root and brief were created. No live peer findings were inspected.\n\n'
            + 'The actual T3 dispatch confirms codex/gpt-6-astra, reasoningEffort=high, serviceTier=default, running with no pending question or approval. Source062 is one distinct research family; its actual proofs remain assigned reading, not a parent-verified deduction. Private navigation and source materials remain unstaged. Reading/navigation limits and exact provenance are recorded in progress-2026-10-22-owner-recovery/reconciliation.json.\n')
(O / 'private/journal-append.bin').write_bytes(appendix.encode())
# Compare again immediately before shared writes; no foreign state may be overwritten.
assert TP.read_bytes() == old_bytes and JP.read_bytes() == old_journal
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=P, text=True).strip() == base['head']
dump(TP, new)
JP.write_bytes(old_journal + appendix.encode())
print(json.dumps({'new_task_index': 648, 'tasks': len(new['tasks']), 'changed_snapshot_keys': changed_snapshot_keys, 'count': new['newAccepted'], 'remaining': new['remaining']}))
