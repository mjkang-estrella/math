#!/usr/bin/env python3
"""Register actual distinct Structural239 discovery; preserve all prior tasks."""
from pathlib import Path
import copy
import datetime
import fnmatch
import hashlib
import json
import os

P = Path(__file__).resolve().parent
C = P.parents[1]
PROJECT = C.parents[2]
read = lambda p: json.loads(p.read_bytes())
sha = lambda b: hashlib.sha256(b).hexdigest()
d = read(P / 'dispatch.json')
br = read(P / 'brief-record.json')
iso = read(P / 'prospective-isolation.json')
owner = '164b1204-be68-4540-94bb-0b91055c4381'
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
assert read(P / 'runtime.json')['parentThreadId'] == owner
assert d['status'] in ('queued', 'running')
assert d['providerInstanceId'] == 'codex' and d['model'] == 'gpt-6-astra'
assert {x['id']: x['value'] for x in d['options']} == {'reasoningEffort': 'xhigh', 'serviceTier': 'default'}
brief = (PROJECT / br['brief']).read_bytes()
assert len(brief) == br['brief_bytes'] == 62139
assert sha(brief) == br['brief_sha256'] == '857a0b85c55124f86c92de9ac95285ead4ce8876a856a3f317e077eec59aa386'
assert len(iso['paths_absent_before_creation']) == 3
assert all(x['literal_present'] for x in iso['foreign_initial_brief_checks'])
assert all(fnmatch.fnmatchcase(x.casefold(), iso['required_literal']) for x in iso['paths_absent_before_creation'])

registry = C / 'tasks.json'
ledger = PROJECT / 'frontier/NEW-TEN-2026-10-14.md'
raw = registry.read_bytes()
lr = ledger.read_bytes()
t = json.loads(raw)
old = copy.deepcopy(t)
assert (t['newAccepted'], t['latestAcceptance'], t['remaining']) == (19, 'R041', 1)
assert t['tasks'][798]['parent_disposition'] == 'CLOSED_PASS_TECHNICAL'
assert not any(x.get('taskId') == d['taskId'] or x.get('brief') == br['brief'] for x in t['tasks'])
idx = len(t['tasks'])
rel = str(P.relative_to(C))
entry = dict(
    d, parent_thread=owner, role='discovery', round=239,
    clientRequestId='twenty-20261025-fresh-structural-r239-codex-astra-r1',
    source_index=364, source_title='Kinetic limits and fluctuations over the regular Boltzmann lifespan',
    output=br['output'], brief=br['brief'], brief_sha256=br['brief_sha256'], brief_bytes=br['brief_bytes'],
    parent_count_at_dispatch=19, accepted=False, count_change=0, publication='STOPPED',
    dispatch_receipt=rel + '/dispatch.json', prospective_isolation=rel + '/prospective-isolation.json',
    isolation_wrapper='structural-r220-isolated-continuation',
    foreign_initial_exclusion_literal='*structural*r220*',
    status_provenance='Actual async dispatch response only; no subsequent liveness poll.',
    parent_full_intake_pending=True,
)
assert entry['output'].rstrip('/') in iso['paths_absent_before_creation']
t['tasks'].append(entry)
note = 'Structural238 CLOSED at full unchanged PASS/TECHNICAL scope, correctness condition discharged at parent level, zero acceptance/count. Distinct Structural239 discovery dispatched on Source364 kinetic limits and fluctuations over the regular Boltzmann lifespan. Codex/GPT-6 Astra/xhigh/default. No new theorem or grade. Campaign19/20,latestR041,one remaining; publication STOPPED.'
t['last_parent_progress'] = note
s = t['current_work_snapshot']
s.update(observed_utc=now, note=note)
s['structural239_dispatch'] = {
    'task_index': idx, 'taskId': d['taskId'], 'status': d['status'], 'source_index': 364,
    'brief': br['brief'], 'brief_sha256': br['brief_sha256'], 'output': entry['output'],
    'dispatch_receipt': entry['dispatch_receipt'], 'isolation_wrapper': entry['isolation_wrapper'], 'count_change': 0,
}
if 'active_task_indices' in s:
    s['active_task_indices'] = [*s['active_task_indices'], idx]
if 't3_last_polled_running' in s:
    s['t3_last_polled_running'] = [*s['t3_last_polled_running'], d['taskId']]
assert t['tasks'][:-1] == old['tasks']
assert all(t[k] == old[k] for k in old if k not in ('tasks', 'current_work_snapshot', 'last_parent_progress'))
assert all(s[k] == v for k, v in old['current_work_snapshot'].items() if k not in ('observed_utc', 'note', 'active_task_indices', 't3_last_polled_running'))

heading = '## Structural239 distinct discovery dispatched: Source364 kinetic limits and fluctuations'
assert heading.encode() not in lr
append = '\n## Structural239 distinct discovery dispatched: Source364 kinetic limits and fluctuations\n\nFollowing Structural238 closure at full unchanged PASS/TECHNICAL scope, a distinct discovery task was dispatched on Source364, kinetic limits and fluctuations over the regular Boltzmann lifespan. The actual receipt confirms **Codex/GPT-6 Astra/xhigh/default**, matching freshly queried capabilities. [Complete brief](campaigns/2026-10-14/expanded-target-2026-10-17/fresh-structural-r220-isolated-r239-brief.txt) and [dispatch receipt](campaigns/2026-10-14/structural-r220-isolated-continuation/discovery-structural-r239-parent/dispatch.json). No S238 repair, narrower resubmission or review shopping is authorized.\n\nBefore any new root or brief existed, parent refreshed original foreign INITIAL brief hash/literal checks from the union of snapshot active indices and explicit foreign-parent queued/running/waiting registry metadata. All planned paths match the pre-existing full-path *structural*r220* exclusion. No foreign liveness or mathematical body was inspected. All399 inherited wildcard/no-r patterns and162 substring guards remain, with the new pair bringing the total to401. No sealed root or closed theorem is reused.\n\nParent displayed only exact Source364 catalogue bytes [611940,614322),2382bytes, using one bounded16000-byte navigation read. No adjacent entry body was displayed. The complete-tree Boltzmann-and-(Grad-or-fluctuations) metadata filter identifies two canonical papers,33entries including eight folders and25blobs. Parent read no source theorem/proof body. Exact owned-registry metadata and narrow inherited-guard checks found no explicit Source364 row or matching topic literal, without establishing historical clearance.\n\nThe child must read both full operative source constructions and strongest compatible primary/history arguments before choosing one additional operation. The stable-radial-potential nonlinear kinetic limit and hard-sphere finite-dimensional Gaussian fluctuation result, with all their internal estimates, are paid. Any extension must preserve the actual grand-canonical/exclusion ensemble, Boltzmann–Grad scaling, regular kinetic interval, exact microscopic centering, collision covariance and relevant history/cutoff constants. Process tightness, bias at fluctuation scale, growing-order estimates and transfer to attractive/singular potentials require genuine compatible proofs. The pinned lean/docs/364.md endpoint is navigation only; no formal support is claimed. No new theorem, grade, acceptance or count assigned. **19/20, latest R041, one remaining; publication STOPPED.**\n'

assert registry.read_bytes() == raw and ledger.read_bytes() == lr
tmp = registry.with_suffix('.structural239.tmp')
tmp.write_text(json.dumps(t, indent=2) + '\n')
assert registry.read_bytes() == raw
os.replace(tmp, registry)
assert ledger.read_bytes() == lr
ledger.write_bytes(lr + append.encode())
out = {
    'observed_utc': now, 'added_task_index': idx, 'taskId': d['taskId'],
    'all_previous_tasks_unchanged': True, 'foreign_snapshot_entries_preserved': True,
    'count_change': 0, 'status_from_actual_dispatch_only': True,
    'all_new_paths_prospectively_covered_by_original_foreign_literal': True,
}
(P / 'integration-record.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
