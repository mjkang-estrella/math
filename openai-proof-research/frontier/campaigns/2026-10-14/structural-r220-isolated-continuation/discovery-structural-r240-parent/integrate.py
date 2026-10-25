#!/usr/bin/env python3
"""Register actual distinct Structural240 discovery; preserve all prior tasks."""
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
assert len(brief) == br['brief_bytes'] == 62188
assert sha(brief) == br['brief_sha256'] == 'd32dd2f56492ab555fb19dde7f99f5f81037265e09284a2c80f6363d03fbdc70'
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
assert t['tasks'][804]['parent_disposition'] == 'ARCHIVED_PREFREEZE_NO_NOMINEE'
assert not any(x.get('taskId') == d['taskId'] or x.get('brief') == br['brief'] for x in t['tasks'])
idx = len(t['tasks'])
rel = str(P.relative_to(C))
entry = dict(
    d, parent_thread=owner, role='discovery', round=240,
    clientRequestId='twenty-20261025-fresh-structural-r240-codex-astra-r1',
    source_index=365, source_title='Joint metric and unitary connection recovery from one boundary patch',
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
note = 'Structural239 archived PREFREEZE/no nominee, no grades/count. Distinct Structural240 discovery dispatched on Source365 joint metric and unitary connection recovery from one boundary patch. Codex/GPT-6 Astra/xhigh/default. No new theorem or grade. Campaign19/20,latestR041,one remaining; publication STOPPED.'
t['last_parent_progress'] = note
s = t['current_work_snapshot']
s.update(observed_utc=now, note=note)
s['structural240_dispatch'] = {
    'task_index': idx, 'taskId': d['taskId'], 'status': d['status'], 'source_index': 365,
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

heading = '## Structural240 distinct discovery dispatched: Source365 inverse boundary recovery'
assert heading.encode() not in lr
append = '\n## Structural240 distinct discovery dispatched: Source365 inverse boundary recovery\n\nAfter Structural239 was archived PREFREEZE/no nominee, a distinct discovery task was dispatched on Source365 joint metric and unitary connection recovery from one boundary patch. Actual dispatch confirms **Codex/GPT-6 Astra/xhigh/default**, matching freshly queried capabilities. [Complete brief](campaigns/2026-10-14/expanded-target-2026-10-17/fresh-structural-r220-isolated-r240-brief.txt) and [dispatch receipt](campaigns/2026-10-14/structural-r220-isolated-continuation/discovery-structural-r240-parent/dispatch.json). No old frozen scope is reopened.\n\nBefore new roots or brief existed, parent refreshed original foreign INITIAL brief hash/literal checks from snapshot active indices union explicit foreign-parent queued/running/waiting registry metadata. Planned paths match pre-existing *structural*r220*. No foreign liveness or mathematical body was inspected. All401 inherited wildcard/no-r patterns and162 substring guards remain; the new pair gives403.\n\nParent displayed exact Source365 catalogue bytes [614322,616826),2504bytes. Two bounded16000-byte probes were used: the first failed to match Markdown numbered headings and displayed only the first180bytes within365; the second displayed only the exact365entry. No adjacent entry body was displayed. A broad tree metadata filter returned unrelated filenames; the operative selection was refined to the three exact catalogue prefixes,44entries including10folders and34blobs. Parent read no source theorem/proof body; owned registry and narrow guard metadata checks give no history clearance.\n\nThe child must read all three complete operative proofs and strongest compatible primary/history mechanisms before selecting one additional operation. Joint rank-two metric/connection recovery, same-patch smooth anisotropic uniqueness and measurable scalar nonuniqueness, including all internal estimates and parameter freedoms, are paid. Exact gauge/diffeomorphism equivalence, measured support and trace spaces, regularity, topology and quantitative uniformity must be maintained. The source365 Lean endpoint is navigation only; no proved formal support is claimed. No new theorem, grade, acceptance or count assigned. **19/20, latest R041, one remaining; publication STOPPED.**\n'

assert registry.read_bytes() == raw and ledger.read_bytes() == lr
tmp = registry.with_suffix('.structural240.tmp')
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
