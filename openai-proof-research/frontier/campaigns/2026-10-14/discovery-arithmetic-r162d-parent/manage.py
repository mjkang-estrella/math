#!/usr/bin/env python3
"""Integrate this notified completion and the single distinct dispatch."""
from pathlib import Path
import copy
import datetime
import hashlib
import json
import re
import subprocess

p = Path.cwd()
b = p / 'frontier/campaigns/2026-10-14'
o = b / 'discovery-arithmetic-r162d-parent'
a = b / 'fresh-arithmetic-discovery-r162d'
tpath = b / 'tasks.json'
jpath = p / 'frontier/NEW-TEN-2026-10-14.md'
baseline = json.loads((o / 'integration-baseline.json').read_bytes())
def git(*args):
    return subprocess.check_output(['git', *args])
def sha(data):
    return hashlib.sha256(data).hexdigest()
def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')
def root_snapshot():
    return {f.relative_to(a).as_posix(): {'bytes': f.stat().st_size, 'sha256': sha(f.read_bytes()), 'mode': f.stat().st_mode} for f in a.rglob('*') if f.is_file()}
assert root_snapshot() == json.loads((o / 'private/root-before.json').read_bytes())
for rel, digest in baseline['protected'].items():
    assert sha((p / rel).read_bytes()) == digest
assert not git('diff', '--cached', '--name-only')
head = git('rev-parse', 'HEAD').decode().strip()
old_t = git('show', head + ':openai-proof-research/' + tpath.relative_to(p).as_posix())
old_j = git('show', head + ':openai-proof-research/' + jpath.relative_to(p).as_posix())
assert old_t == tpath.read_bytes() and old_j == jpath.read_bytes(), 'Another owner has uncommitted coordination writes; stop without overwriting.'
base_tasks = json.loads(old_t)
tasks = copy.deepcopy(base_tasks)
assert tasks['newAccepted'] == 19 and tasks['target'] == 20 and tasks['remaining'] == 1 and tasks['latestAcceptance'] == 'R041'
terminal = json.loads((o / 'task-status.json').read_bytes())['structuredContent']
dispatch = json.loads((o / 'arithmetic-r162e-dispatch.json').read_bytes())['structuredContent']
args = json.loads((o / 'private/submitted-prompt.json').read_bytes())
assert terminal['status'] == 'completed' and terminal['workState'] == 'result_available'
assert dispatch['status'] == 'running' and dispatch['workState'] == 'working'
for result in [terminal, dispatch]:
    assert result['providerInstanceId'] == 'codex' and result['model'] == 'gpt-6-astra'
    assert {x['id']: x['value'] for x in result['options']} == {'reasoningEffort': 'high', 'serviceTier': 'default'}
    assert not result['hasPendingChildRuns'] and not result['hasPendingQuestion'] and result['pendingApproval'] is None
assert not any(x.get('taskId') == dispatch['taskId'] or x.get('clientRequestId') == args['clientRequestId'] for x in tasks['tasks'])
old_indices = [i for i,x in enumerate(tasks['tasks']) if x.get('taskId') == terminal['taskId']]
assert old_indices == [656]
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
tasks['tasks'][656].update(terminal)
tasks['tasks'][656].update({'observed_utc': now, 'status_provenance': 'Single actual notified terminal task_status response; final result available, no pending child/question/approval.', 'parent_intake': 'discovery-arithmetic-r162d-parent/intake.json', 'parent_disposition': 'PREFREEZE_NO_NOMINEE_ARCHIVED', 'accepted': False, 'count_change': 0})
brief_path = b / 'expanded-target-2026-10-17/fresh-arithmetic-r162e-brief.txt'
brief = brief_path.read_bytes()
assert args['task'].encode() == brief
prep = json.loads((o / 'brief-preparation.json').read_bytes())
assert sha(brief) == prep['sha256'] and len(brief) == prep['bytes']
new = copy.deepcopy(dispatch)
new.update({'observed_utc': now, 'target': args['target'], 'role': args['role'], 'title': args['title'], 'output': 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162e/', 'brief': brief_path.relative_to(p).as_posix(), 'brief_sha256': sha(brief), 'brief_bytes': len(brief), 'source_family_navigation': 'Source068; exact catalogue[115750,121339), seven companion folders,115 descendants/94 blobs. Metadata navigation only; actual operative-proof reading assigned.', 'round_namespace': 'NEW DISTINCT Source068 family inside previously excluded arithmetic162 namespace; no retry/restriction of162d or older scopes.', 'parent_count_at_dispatch': 19, 'accepted': False, 'count_change': 0, 'publication': 'STOPPED', 'dispatch_receipt': 'discovery-arithmetic-r162d-parent/arithmetic-r162e-dispatch.json', 'prospective_isolation': 'discovery-arithmetic-r162d-parent/prospective-isolation-arithmetic162e.json', 'clientRequestId': args['clientRequestId'], 'round': 1, 'parent_thread': '6742db91-d35c-44d0-a762-e5d9232f5177', 'status_provenance': 'Actual successful delegate_task response; running at dispatch, not a later liveness poll.'})
new_index = len(tasks['tasks'])
tasks['tasks'].append(new)
note = f'Arithmetic162d(idx656, Source067) completed PREFREEZE/no nominee and archived: the Grassmannian/Poincare family obstructs prescribed compact-parameter relative flat transport even after compatible finite etale covers; classical negative feasibility, no substantial nominee. Exact57-file verification and15 canonical blob checks passed; no grade/count. Arithmetic162e(idx{new_index}, DISTINCT Source068 anticanonical-nonvanishing family, seven companions) dispatched with Astra high/default inside the already excluded162 namespace. Foreign owner tasks and prior archives preserved without status queries, live-body inspection or steering. Campaign19/20, latestR041, one remains; publication STOPPED.'
tasks['last_parent_progress'] = note
snapshot = tasks['current_work_snapshot']
snapshot.update({'observed_utc': now, 'note': note, 'accepted_count': 19, 'remaining': 1, 'publication': 'STOPPED'})
snapshot['t3_current_confirmed_running'] = [x for x in snapshot.get('t3_current_confirmed_running', []) if x != terminal['taskId']]
snapshot['t3_current_confirmed_running'].append(dispatch['taskId'])
snapshot.setdefault('t3_dispatch_observations', []).append({'observed_utc': now, **dispatch})
snapshot['arithmetic_r162d_archive'] = {'task_index': 656, 'status': 'PREFREEZE_NO_NOMINEE_ARCHIVED', 'intake': 'discovery-arithmetic-r162d-parent/intake.json', 'accepted': False, 'count_change': 0}
old_guards = set(re.findall(rb'\*[^\s,;()]*\*', (b / 'expanded-target-2026-10-17/fresh-arithmetic-r162d-brief.txt').read_bytes()))
assert old_guards <= set(re.findall(rb'\*[^\s,;()]*\*', brief))
marker = b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
assert brief.split(marker,1)[1] == (b / 'expanded-target-2026-10-17/fresh-arithmetic-r162d-brief.txt').read_bytes().split(marker,1)[1]
iso = json.loads((o / 'prospective-isolation-arithmetic162e.json').read_bytes())
for peer in iso['peer_original_initial_briefs']:
    assert sha((p / peer['brief']).read_bytes()) == peer['brief_sha256']
for i, task in enumerate(base_tasks['tasks']):
    if i != 656:
        assert tasks['tasks'][i] == task
for k, v in base_tasks.items():
    if k not in ['tasks', 'last_parent_progress', 'current_work_snapshot']:
        assert tasks[k] == v
append = ('\n\n### Arithmetic162d archived; distinct Arithmetic162e dispatched\n\n' + note + '\n\nThe 57-file packet (6,192,272 bytes), three external anchors and fifteen canonical Git bindings matched; all84 author-root files remained unchanged. The author reports fourteen textual canonical bodies read and PDF authentication only. Late primary completions/rendered confirmation, clipping recovery, selective antecedent/history coverage and scan limitations are disclosed. The first parent oversized coordination display was recovered with a focused first-note read. These artifact checks assign no mathematical gate.\n\nParent assessment: frontier/campaigns/2026-10-14/discovery-arithmetic-r162d-parent/assessment.md. Separate Source068 discovery uses the exact[115750,121339) catalogue body and all seven stipulated companion proofs; existing scopes remain immutable. New task running was observed only at successful dispatch. Foreign Structural195 is recorded-running under its owner, not freshly queried here. Its original initial162 wildcard covered the new namespace prospectively. No public or downstream work.\n').encode()
assert head == git('rev-parse','HEAD').decode().strip() and old_t == tpath.read_bytes() and old_j == jpath.read_bytes()
write(o / 'coordination-rebase.json', {'initial_head': baseline['head'], 'integration_head': head, 'rebased': head != baseline['head'], 'baseline_tasks': len(base_tasks['tasks']), 'new_task_index': new_index, 'completed_task_index': 656, 'preserved_other_tasks': len(base_tasks['tasks'])-1, 'foreign_status_not_queried': True})
write(tpath, tasks)
jpath.write_bytes(old_j + append)
assert jpath.read_bytes()[:len(old_j)] == old_j
write(o / 'private/journal-append.json', {'prior_bytes': len(old_j), 'prior_sha256': sha(old_j), 'append_bytes': len(append), 'append_sha256': sha(append)})
stage = [tpath, jpath, brief_path, a/'ANCHORS.json', a/'REPORT.md', a/'packet/FINAL.md', a/'packet/notes/01-operative-integration.md', a/'packet/notes/02-prefreeze-relative-transport.md', a/'packet/verify_packet.py']
stage += [o / name for name in ['integration-baseline.json','task-status.json','capabilities.json','verification.json','prospective-isolation-arithmetic162e.json','assessment.md','intake.json','prepare-brief.py','brief-preparation.json','arithmetic-r162e-dispatch.json','manage.py','coordination-rebase.json','integration-guard.json']]
relative = [f.relative_to(p).as_posix() for f in stage]
assert all('/private/' not in f and not f.endswith('MANIFEST.json') and '/controls/' not in f for f in relative)
guard = {'baseline_head': head, 'completed_task_index':656, 'new_task_index':new_index, 'old_tasks_preserved_except656':True, 'old_top_level_preserved_except_progress_snapshot':True, 'journal_prefix_unchanged':True, 'author_root84files_unchanged':True, 'anchors_and15canonical_bindings_match':True, 'original_standing_brief5570bytes_unchanged':True, 'old_literal_guards_preserved':len(old_guards), 'new_runtime_verified':'codex/gpt-6-astra/high/default; running at dispatch; no pending child/question/approval', 'foreign_initial_guard_before_new_root_brief':True, 'foreign_liveness_not_queried':True, 'count':19, 'target':20, 'remaining':1, 'latestAcceptance':'R041', 'publication':'STOPPED', 'stage_allowlist':relative, 'protected_excluded':baseline['protected']}
write(o/'integration-guard.json', guard)
assert root_snapshot() == json.loads((o / 'private/root-before.json').read_bytes())
assert head == git('rev-parse','HEAD').decode().strip()
subprocess.run(['git','add','--',*relative],check=True)
staged = git('diff','--cached','--name-only').decode().splitlines()
expected = {'openai-proof-research/'+x for x in relative}
assert set(staged) == expected
for rel in relative:
    assert git('show',':openai-proof-research/'+rel) == (p/rel).read_bytes()
print(json.dumps({'status':'INTEGRATED_AND_STAGED','new_task_index':new_index,'staged_files':len(staged),'newAccepted':19,'remaining':1,'head':head},indent=2))
