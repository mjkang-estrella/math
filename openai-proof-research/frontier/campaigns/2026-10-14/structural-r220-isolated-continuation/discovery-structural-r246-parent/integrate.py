#!/usr/bin/env python3
"""Register actual distinct Structural246 discovery; preserve all prior tasks."""
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
assert len(brief) == br['brief_bytes'] == 66538
assert sha(brief) == br['brief_sha256'] == '26e518f102275300065acdbaf51a21f3b1ec846ab0d83c9943848ac5d16a8548'
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
assert t['tasks'][816]['parent_disposition'] == 'ARCHIVED_PREFREEZE_NO_NOMINEE'
assert not any(x.get('taskId') == d['taskId'] or x.get('brief') == br['brief'] for x in t['tasks'])
idx = len(t['tasks'])
rel = str(P.relative_to(C))
entry = dict(
    d, parent_thread=owner, role='discovery', round=246,
    clientRequestId='twenty-20261025-fresh-structural-r246-codex-astra-r1',
    source_index=371, source_title='Stable defocusing Schrödinger blowup',
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
note = 'Structural245 archived PREFREEZE/no nominee, no grades/count. Distinct Structural246 discovery dispatched on Source371 Stable defocusing Schrödinger blowup. Codex/GPT-6 Astra/xhigh/default confirmed. No new theorem or grade. Campaign19/20,latestR041,one remaining; publication STOPPED.'
t['last_parent_progress'] = note
s = t['current_work_snapshot']
s.update(observed_utc=now, note=note)
s['structural246_dispatch'] = {
    'task_index': idx, 'taskId': d['taskId'], 'status': d['status'], 'source_index': 371,
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

heading = '## Structural246 distinct discovery dispatched: Source371 stable defocusing Schrödinger blowup'
assert heading.encode() not in lr
append = '\n## Structural246 distinct discovery dispatched: Source371 stable defocusing Schrödinger blowup\n\nAfter Structural245 was archived PREFREEZE/no nominee, a distinct discovery task was dispatched on Source371 stable self-similar defocusing NLS blowup. The actual response confirms **Codex/GPT-6 Astra/xhigh/default (standard speed)**, matching fresh capabilities and the latest explicit user preference. [Complete brief](campaigns/2026-10-14/expanded-target-2026-10-17/fresh-structural-r220-isolated-r246-brief.txt) and [dispatch receipt](campaigns/2026-10-14/structural-r220-isolated-continuation/discovery-structural-r246-parent/dispatch.json). No old frozen scope is reopened.\n\nBefore creating any new root or brief, parent refreshed original foreign INITIAL brief hash/literal checks from the union of snapshot active indices and explicit foreign-parent queued/running/waiting registry metadata. All planned paths match existing *structural*r220*. No foreign liveness or mathematical body was inspected. All413 inherited wildcard/no-r patterns and162 substrings remain; the new pair gives415.\n\nOnly Source371 catalogue bytes [622975,624110),1135bytes, were displayed from one bounded16000-byte navigation read. No adjacent entry body was displayed. The complete-tree exact-title filter identifies one root,24entries including six directories and18blobs. Parent read no source theorem/proof body. Owned-registry and narrow guard metadata are not historical clearance.\n\nThe child must read the complete source and strongest compatible primary/history mechanisms before selecting one additional operation. The stable open blowup basin, profiles, spectrum, linear/nonlinear machinery, certificate interfaces and Gaussian positive-probability corollary are already paid. Any extension must carry its interaction, modulation, propagation, geometry or probabilistic estimates through the entire proposed scope. No new theorem, grade, acceptance or count is assigned. **19/20, latest R041, one remaining; publication STOPPED.**\n'

assert registry.read_bytes() == raw and ledger.read_bytes() == lr
tmp = registry.with_suffix('.structural246.tmp')
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
