#!/usr/bin/env python3
"""Archive notified partial research and record one unfinished-work continuation."""
from pathlib import Path
import copy
import datetime
import hashlib
import json
import re
import subprocess

p = Path.cwd()
b = p / 'frontier/campaigns/2026-10-14'
o = b / 'discovery-arithmetic-r162j-parent'
a = b / 'fresh-arithmetic-discovery-r162j'
tpath = b / 'tasks.json'
jpath = p / 'frontier/NEW-TEN-2026-10-14.md'
git = lambda *args: subprocess.check_output(['git', *args])
sha = lambda data: hashlib.sha256(data).hexdigest()
load = lambda path: json.loads(path.read_bytes())

def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')

def snapshot_root():
    return {f.relative_to(a).as_posix(): {
        'bytes': f.stat().st_size, 'mode': f.stat().st_mode, 'sha256': sha(f.read_bytes())
    } for f in a.rglob('*') if f.is_file()}

baseline = load(o / 'integration-baseline.json')
assert (o / 'capabilities.json').is_file()
assert snapshot_root() == load(o / 'private/root-before.json')
for rel, digest in baseline['protected'].items():
    assert sha((p / rel).read_bytes()) == digest
assert not git('diff', '--cached', '--name-only')
head = git('rev-parse', 'HEAD').decode().strip()
old_t = git('show', head + ':openai-proof-research/' + tpath.relative_to(p).as_posix())
old_j = git('show', head + ':openai-proof-research/' + jpath.relative_to(p).as_posix())
assert tpath.read_bytes() == old_t and jpath.read_bytes() == old_j, 'Other owner has uncommitted coordination writes; do not overwrite.'
base_tasks = json.loads(old_t)
tasks = copy.deepcopy(base_tasks)
assert (tasks['newAccepted'], tasks['target'], tasks['remaining'], tasks['latestAcceptance']) == (19, 20, 1, 'R041')
terminal = load(o / 'task-status.json')['structuredContent']
dispatch = load(o / 'continuation-dispatch.json')['structuredContent']
args = load(o / 'private/submitted-prompt.json')
assert terminal['status'] == 'completed' and terminal['workState'] == 'result_available'
assert dispatch['status'] == 'running' and dispatch['workState'] == 'working'
for d in [terminal, dispatch]:
    assert d['providerInstanceId'] == 'codex' and d['model'] == 'gpt-6-astra'
    assert {x['id']: x['value'] for x in d['options']} == {'reasoningEffort': 'high', 'serviceTier': 'default'}
    assert not d['hasPendingChildRuns'] and not d['hasPendingQuestion'] and d['pendingApproval'] is None
assert [i for i, x in enumerate(tasks['tasks']) if x.get('taskId') == terminal['taskId']] == [664]
assert not any(x.get('taskId') == dispatch['taskId'] or x.get('clientRequestId') == args['clientRequestId'] for x in tasks['tasks'])
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
tasks['tasks'][664].update(terminal)
tasks['tasks'][664].update({
    'observed_utc': now, 'parent_intake': 'discovery-arithmetic-r162j-parent/intake.json',
    'parent_disposition': 'PREFREEZE_NO_NOMINEE_READING_INCOMPLETE',
    'status_provenance': 'Single actual notified terminal response; no pending child/question/approval.',
    'accepted': False, 'count_change': 0,
})
brief_path = b / 'expanded-target-2026-10-17/arithmetic-r162j-continuation-r1-brief.txt'
brief = brief_path.read_bytes()
prep = load(o / 'brief-preparation.json')
assert args['task'].encode() == brief and sha(brief) == prep['sha256'] and len(brief) == prep['bytes']
new = copy.deepcopy(dispatch)
new.update({
    'observed_utc': now, 'target': args['target'], 'role': args['role'], 'title': args['title'],
    'output': 'frontier/campaigns/2026-10-14/arithmetic-r162j-continuation-r1/',
    'brief': brief_path.relative_to(p).as_posix(), 'brief_sha256': sha(brief), 'brief_bytes': len(brief),
    'source_family_navigation': 'SAME Source074 exact catalogue[126238,127638), two canonical folders/35 blobs. No new family selection; incomplete operative reading must be completed before further extended deductions.',
    'round_namespace': 'Fresh-root continuation of unfinished Arithmetic162j full-scope research; NOT a new-family claim or review/grade retry. Original sealed packet immutable.',
    'predecessor_task_index': 664, 'original_full_target': 'UNCHANGED_UNPROVED_4D_L4_KAKEYA_MAXIMAL',
    'parent_count_at_dispatch': 19, 'accepted': False, 'count_change': 0, 'publication': 'STOPPED',
    'dispatch_receipt': 'discovery-arithmetic-r162j-parent/continuation-dispatch.json',
    'prospective_isolation': 'discovery-arithmetic-r162j-parent/prospective-isolation-continuation.json',
    'clientRequestId': args['clientRequestId'], 'round': 1, 'research_continuation': True,
    'parent_thread': '6742db91-d35c-44d0-a762-e5d9232f5177',
    'status_provenance': 'Actual successful delegate_task response; running at dispatch, not a later liveness poll.',
})
new_index = len(tasks['tasks'])
tasks['tasks'].append(new)
note = f'Arithmetic162j(idx664) completed PREFREEZE/no nominee: capped-Jacobian/K3 calculations retain a substantial-mass overlap gap for the unchanged full4D maximal target. Central canonical and recursive primary reading remains INCOMPLETE; no strongest-payment clearance or grade/count adopted. Exact91-file/35-canonical verification passed; all93 completed-root files unchanged. Fresh-root continuation(idx{new_index}) dispatched with Astra high/default to FINISH missing operative reading before further sustained mathematics at the SAME full target; no new-family claim,restriction or grade retry. Other-owner committed task changes preserved without live status/body inspection or steering. Campaign19/20,latestR041,one remains; publication STOPPED.'
tasks['last_parent_progress'] = note
s = tasks['current_work_snapshot']
s.update({'observed_utc': now, 'note': note, 'accepted_count': 19, 'remaining': 1, 'publication': 'STOPPED'})
s['t3_current_confirmed_running'] = [x for x in s.get('t3_current_confirmed_running', []) if x != terminal['taskId']]
s['t3_current_confirmed_running'].append(dispatch['taskId'])
s.setdefault('t3_dispatch_observations', []).append({'observed_utc': now, **dispatch})
s['arithmetic_r162j_archive'] = {'task_index': 664, 'status': 'PREFREEZE_NO_NOMINEE_READING_INCOMPLETE', 'intake': 'discovery-arithmetic-r162j-parent/intake.json', 'count_change': 0, 'continuation_task_index': new_index}
original = (b / 'expanded-target-2026-10-17/fresh-arithmetic-r162j-brief.txt').read_bytes()
assert brief.endswith(original)
guards = set(re.findall(rb'\*[^\s,;()]*\*', original))
assert guards <= set(re.findall(rb'\*[^\s,;()]*\*', brief))
marker = b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
assert brief.split(marker, 1)[1] == original.split(marker, 1)[1]
assert len(brief.split(marker, 1)[1]) == 5570
iso = load(o / 'prospective-isolation-continuation.json')
for peer in iso['peer_original_initial_briefs']:
    assert sha((p / peer['brief']).read_bytes()) == peer['brief_sha256']
for i, old in enumerate(base_tasks['tasks']):
    if i != 664:
        assert tasks['tasks'][i] == old
for k, v in base_tasks.items():
    if k not in ['tasks', 'last_parent_progress', 'current_work_snapshot']:
        assert tasks[k] == v
append = ('\n\n### Arithmetic162j incomplete-reading intake; full-scope continuation dispatched\n\n' + note + '\n\nThe full target remains every-epsilon L4(R4)->L4(S3) maximal control for all functions,centers and arbitrary measurable shadings. Monic-cubic Jacobian payment,capped transport,K3 directional-marginal estimates,fixed-normal ranges and the primary baseline are preserved. Substantial-mass overlap or compatible hidden-density control remains unpaid; normalizing a sparse successful event loses original product-prior domination. No restricted result or worldwide impossibility claim.\n\nAll91 payload files (3,905,880 bytes), three detached anchors and35 complete-tree canonical bindings matched. Four completed originals,three direct instruction spans,two original whole/span pairs and three primary text bindings rechecked; five saved copied controls matched. All93 original-root files retained bytes/modes. These are artifact checks only. Author canonical semantic coverage265,136/1,019,669text bytes leaves central K3/K4 and recursive primary proofs unread; complete operative-reading prerequisite NOT attained. No full-scope strongest-proof clearance is adopted.\n\nParent assessment: frontier/campaigns/2026-10-14/discovery-arithmetic-r162j-parent/assessment.md. Continuation in a new exclusive root must finish actual operative proof reading before further extended deductions,then continue the SAME unchanged full target with the original assignment,calculations,failures and exact gaps. Original sealed root is immutable; no independent reviews or downstream work on an unproved theorem. All old scopes and fullPASS/TECHNICAL zero-count closures preserved. Foreign recorded initial briefs were checked prospectively without reading live findings or querying liveness. Concurrent other-owner changes were adopted only from committed coordination state and otherwise preserved.\n').encode()
assert head == git('rev-parse', 'HEAD').decode().strip()
assert tpath.read_bytes() == old_t and jpath.read_bytes() == old_j
write(o / 'coordination-rebase.json', {
    'initial_head': baseline['head'], 'integration_head': head, 'rebased': head != baseline['head'],
    'initial_tasks': baseline['taskCount'], 'integration_tasks': len(base_tasks['tasks']),
    'completed_task_index': 664, 'new_task_index': new_index,
    'preserved_other_tasks': len(base_tasks['tasks']) - 1, 'foreign_liveness_not_queried': True,
})
write(tpath, tasks)
jpath.write_bytes(old_j + append)
write(o / 'private/journal-append.json', {'prior_bytes': len(old_j), 'prior_sha256': sha(old_j), 'append_bytes': len(append), 'append_sha256': sha(append)})
assert jpath.read_bytes().startswith(old_j)
stage = [tpath, jpath, brief_path, a / 'REPORT.md', a / 'packet/FINAL.md',
         a / 'packet/NOTES.md', a / 'packet/PREFREEZE.md', a / 'packet/verify_packet.py']
stage += [o / x for x in ['integration-baseline.json', 'task-status.json', 'capabilities.json',
    'verification.json', 'assessment.md', 'intake.json', 'verify-intake.py',
    'prospective-isolation-continuation.json', 'prepare-continuation.py', 'brief-preparation.json',
    'continuation-dispatch.json', 'manage.py', 'coordination-rebase.json', 'integration-guard.json']]
relative = [f.relative_to(p).as_posix() for f in stage]
assert all('/private/' not in x and not x.endswith('MANIFEST.json') and '/controls/' not in x for x in relative)
write(o / 'integration-guard.json', {
    'baseline_head': head, 'completed_task_index': 664, 'new_task_index': new_index,
    'old_tasks_preserved_except664': True, 'other_top_level_preserved_except_progress_snapshot': True,
    'journal_prefix_preserved': True, 'completed_root93files_unchanged': True,
    'artifact_checks': '91 files/35 canonical blobs/three anchors match; not mathematical gates',
    'operative_reading_prerequisite': 'NOT_ATTAINED; continuation explicitly required',
    'original_assignment_and_standing5570bytes_preserved': True, 'old_guards_retained': len(guards),
    'new_runtime': 'codex/gpt-6-astra/high/default; actual running dispatch; no pending child/question/approval',
    'same_full_target_unchanged': True, 'new_family_or_grade_retry': False,
    'prospective_foreign_initial_briefs_checked': len(iso['peer_original_initial_briefs']),
    'foreign_liveness_not_queried': True, 'count': 19, 'remaining': 1, 'latestAcceptance': 'R041',
    'publication': 'STOPPED', 'stage_allowlist': relative, 'protected_excluded': baseline['protected'],
})
assert snapshot_root() == load(o / 'private/root-before.json')
assert head == git('rev-parse', 'HEAD').decode().strip()
subprocess.run(['git', 'add', '--', *relative], check=True)
assert set(git('diff', '--cached', '--name-only').decode().splitlines()) == {'openai-proof-research/' + x for x in relative}
for rel in relative:
    assert git('show', ':openai-proof-research/' + rel) == (p / rel).read_bytes()
print(json.dumps({'status': 'INTEGRATED_AND_STAGED', 'head': head, 'new_task_index': new_index,
                  'staged_files': len(relative), 'count': 19, 'remaining': 1}, indent=2))
