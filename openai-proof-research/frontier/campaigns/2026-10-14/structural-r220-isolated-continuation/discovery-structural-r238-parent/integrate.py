#!/usr/bin/env python3
"""Register actual distinct Structural238 discovery; preserve all prior tasks."""
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
assert len(brief) == br['brief_bytes'] == 60642
assert sha(brief) == br['brief_sha256'] == 'b5a3b9a017028075398dc2cae5eb31d763ea916a3f61719f45038c579e319be3'
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
assert t['tasks'][796]['parent_disposition'] == 'ARCHIVED_PREFREEZE_NO_NOMINEE'
assert not any(x.get('taskId') == d['taskId'] or x.get('brief') == br['brief'] for x in t['tasks'])
idx = len(t['tasks'])
rel = str(P.relative_to(C))
entry = dict(
    d, parent_thread=owner, role='discovery', round=238,
    clientRequestId='twenty-20261025-fresh-structural-r238-codex-astra-r1',
    source_index=363, source_title='Hard-sphere Boltzmann nonuniqueness with local conservation',
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
note = ('Structural237 ARCHIVED PREFREEZE/no nominee, with coupled uniqueness and quantitative stability unresolved; no grades or count. '
        'Distinct Structural238 discovery dispatched on Source363 hard-sphere Boltzmann nonuniqueness with local conservation. '
        'Codex/GPT-6 Astra/xhigh/default. No new theorem or grade. Campaign19/20,latestR041,one remaining; publication STOPPED.')
t['last_parent_progress'] = note
s = t['current_work_snapshot']
s.update(observed_utc=now, note=note)
s['structural238_dispatch'] = {
    'task_index': idx, 'taskId': d['taskId'], 'status': d['status'], 'source_index': 363,
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

heading = '## Structural238 distinct discovery dispatched: Source363 hard-sphere Boltzmann'
assert heading.encode() not in lr
append = '''
## Structural238 distinct discovery dispatched: Source363 hard-sphere Boltzmann

Following Structural237 archival at PREFREEZE/no nominee, a distinct discovery task was dispatched on Source363, hard-sphere Boltzmann nonuniqueness with local conservation. S237 retains its integrated H1 trace, common momentum-bound and rough-data compactness derivations; coupled uniqueness and quantitative stability remain unresolved. No mathematical grades or count were assigned to that round. The new actual receipt confirms **Codex/GPT-6 Astra/xhigh/default**, matching fresh live capabilities. [Complete brief](campaigns/2026-10-14/expanded-target-2026-10-17/fresh-structural-r220-isolated-r238-brief.txt) and [dispatch receipt](campaigns/2026-10-14/structural-r220-isolated-continuation/discovery-structural-r238-parent/dispatch.json).

Before creating any new root or brief, parent refreshed original foreign INITIAL brief hash/literal checks from the union of snapshot active indices and explicit foreign-parent queued/running/waiting metadata. Every planned path matches the pre-existing full-path *structural*r220* exclusion. No foreign liveness or mathematical body was inspected. All 397 inherited wildcard/no-r patterns and 162 substring guards remain; the new pair brings the total to 399. No sealed root or closed theorem is reused.

Parent displayed only exact Source363 catalogue bytes [609877,611940), 2063 bytes, from one bounded 16000-byte navigation read. No adjacent body was displayed. The narrowly filtered complete-tree metadata identifies two canonical papers, 43 entries including eight folders and 35 blobs. No source theorem/proof body was read by parent. An exact filter found no explicit owned Source363 row or matching topic string in inherited guards, without establishing history clearance.

The child must read both complete operative pinned constructions, including the later exact-local-conservation theorem, and carry the strongest compatible primary/history mechanisms through any proposed extension. The existing two-solution and internal branching constructions are already paid. Additional branches or parameterizations must preserve one common initial density, actual entropy admissibility, global strong L1 continuity, exact local mass/momentum/energy conservation, every required polynomial collision weight and separation after all limits. No arbitrary restart, nonlinear convex combination or packet independence may be assumed. The pinned lean/docs/363.md endpoint is navigation only; no formal coverage is claimed. No new theorem, grade, acceptance or count assigned. **19/20, latest R041, one remaining; publication STOPPED.**
'''

assert registry.read_bytes() == raw and ledger.read_bytes() == lr
tmp = registry.with_suffix('.structural238.tmp')
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
