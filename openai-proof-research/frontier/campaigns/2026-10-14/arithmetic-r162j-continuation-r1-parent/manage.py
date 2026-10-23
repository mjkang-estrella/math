#!/usr/bin/env python3
"""Integrate the notified continuation and one distinct Source075 dispatch."""
from pathlib import Path
import copy
import datetime
import hashlib
import json
import re
import subprocess

p = Path.cwd()
b = p / 'frontier/campaigns/2026-10-14'
o = b / 'arithmetic-r162j-continuation-r1-parent'
a = b / 'arithmetic-r162j-continuation-r1'
tpath, jpath = b / 'tasks.json', p / 'frontier/NEW-TEN-2026-10-14.md'
git = lambda *args: subprocess.check_output(['git', *args])
sha = lambda d: hashlib.sha256(d).hexdigest()
load = lambda f: json.loads(f.read_bytes())

def write(f, value):
    f.write_text(json.dumps(value, indent=2) + '\n')

def author_snapshot():
    return {f.relative_to(a).as_posix(): {
        'bytes': f.stat().st_size, 'mode': f.stat().st_mode, 'sha256': sha(f.read_bytes())
    } for f in a.rglob('*') if f.is_file()}

baseline = load(o / 'integration-baseline.json')
assert (o / 'capabilities.json').is_file()
assert author_snapshot() == load(o / 'private/root-before.json')
for rel, digest in baseline['protected'].items():
    assert sha((p / rel).read_bytes()) == digest
assert not git('diff', '--cached', '--name-only')
head = git('rev-parse', 'HEAD').decode().strip()
old_t = git('show', head + ':openai-proof-research/' + tpath.relative_to(p).as_posix())
old_j = git('show', head + ':openai-proof-research/' + jpath.relative_to(p).as_posix())
assert tpath.read_bytes() == old_t and jpath.read_bytes() == old_j, 'Other owner coordination is uncommitted; do not overwrite.'
base = json.loads(old_t)
tasks = copy.deepcopy(base)
assert (tasks['newAccepted'], tasks['target'], tasks['remaining'], tasks['latestAcceptance']) == (19, 20, 1, 'R041')
terminal = load(o / 'task-status.json')['structuredContent']
dispatch = load(o / 'arithmetic-r162k-dispatch.json')['structuredContent']
args = load(o / 'private/submitted-prompt.json')
assert terminal['status'] == 'completed' and terminal['workState'] == 'result_available'
assert dispatch['status'] == 'running' and dispatch['workState'] == 'working'
for d in [terminal, dispatch]:
    assert (d['providerInstanceId'], d['model']) == ('codex', 'gpt-6-astra')
    assert {x['id']: x['value'] for x in d['options']} == {'reasoningEffort': 'high', 'serviceTier': 'default'}
    assert not d['hasPendingChildRuns'] and not d['hasPendingQuestion'] and d['pendingApproval'] is None
assert [i for i, x in enumerate(tasks['tasks']) if x.get('taskId') == terminal['taskId']] == [667]
assert not any(x.get('taskId') == dispatch['taskId'] or x.get('clientRequestId') == args['clientRequestId'] for x in tasks['tasks'])
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
tasks['tasks'][667].update(terminal)
tasks['tasks'][667].update({
    'observed_utc': now, 'parent_intake': 'arithmetic-r162j-continuation-r1-parent/intake.json',
    'parent_disposition': 'PREFREEZE_NO_NOMINEE_ARCHIVED',
    'status_provenance': 'Single actual notified terminal task_status response; no pending child/question/approval.',
    'canonical_reading_prerequisite': 'Completed as recorded; bounded primary/transitive limits retained',
    'accepted': False, 'count_change': 0,
})
brief_path = b / 'expanded-target-2026-10-17/fresh-arithmetic-r162k-brief.txt'
brief, prep = brief_path.read_bytes(), load(o / 'brief-preparation.json')
assert args['task'].encode() == brief and len(brief) == prep['bytes'] and sha(brief) == prep['sha256']
new = copy.deepcopy(dispatch)
new.update({
    'observed_utc': now, 'target': args['target'], 'role': args['role'], 'title': args['title'],
    'output': 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162k/',
    'brief': brief_path.relative_to(p).as_posix(), 'brief_sha256': sha(brief), 'brief_bytes': len(brief),
    'source_family_navigation': 'DISTINCT Source075; exact catalogue[127638,128445), one canonical folder,20 descendants/17 blobs; actual build/main.tex. Metadata navigation only; complete operative reading required before extended deductions.',
    'round_namespace': 'NEW DISTINCT Source075 operation inside previously excluded arithmetic162 namespace; no retry/restriction of the unpaid full4D maximal or other old scopes.',
    'parent_count_at_dispatch': 19, 'accepted': False, 'count_change': 0, 'publication': 'STOPPED',
    'dispatch_receipt': 'arithmetic-r162j-continuation-r1-parent/arithmetic-r162k-dispatch.json',
    'prospective_isolation': 'arithmetic-r162j-continuation-r1-parent/prospective-isolation-arithmetic162k.json',
    'clientRequestId': args['clientRequestId'], 'round': 1,
    'parent_thread': '6742db91-d35c-44d0-a762-e5d9232f5177',
    'status_provenance': 'Actual successful delegate_task response; running at dispatch, not a later liveness poll.',
})
new_index = len(tasks['tasks'])
tasks['tasks'].append(new)
note = f'Arithmetic162j continuation(idx667) completed PREFREEZE/no nominee: all1,019,669 canonical non-PDF bytes own-read as recorded,35 blobs authenticate; operative primary/recursive reading completed with explicit limits. Conditional horizontal three-traversal time payment is exactlylambda^4; simultaneous same-mass state/velocity preparation,normal-label/recovery/overlap costs remain unpaid for the UNCHANGED full4D maximal target. Exact106-file verification; all114 completed-root files unchanged; no grade/count. Arithmetic162k(idx{new_index}, DISTINCT Source075 L log L Fourier-convergence family) dispatched with Astra high/default in the already excluded162 namespace. Old full targets and wholePASS/TECHNICAL zero-count closures preserved. Foreign-owner tasks preserved without live status/body inspection or steering. Campaign19/20,latestR041,one remains; publication STOPPED.'
tasks['last_parent_progress'] = note
s = tasks['current_work_snapshot']
s.update({'observed_utc': now, 'note': note, 'accepted_count': 19, 'remaining': 1, 'publication': 'STOPPED'})
s['t3_current_confirmed_running'] = [x for x in s.get('t3_current_confirmed_running', []) if x != terminal['taskId']]
s['t3_current_confirmed_running'].append(dispatch['taskId'])
s.setdefault('t3_dispatch_observations', []).append({'observed_utc': now, **dispatch})
s['arithmetic_r162j_continuation_r1_archive'] = {'task_index': 667, 'status': 'PREFREEZE_NO_NOMINEE_ARCHIVED', 'intake': 'arithmetic-r162j-continuation-r1-parent/intake.json', 'count_change': 0, 'full_target': 'UNCHANGED_UNPROVED', 'canonical_reading': 'COMPLETED_AS_RECORDED'}
previous = (b / 'expanded-target-2026-10-17/fresh-arithmetic-r162j-brief.txt').read_bytes()
guards = set(re.findall(rb'\*[^\s,;()]*\*', previous))
assert guards <= set(re.findall(rb'\*[^\s,;()]*\*', brief))
marker = b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
assert brief.split(marker, 1)[1] == previous.split(marker, 1)[1]
assert len(brief.split(marker, 1)[1]) == 5570
iso = load(o / 'prospective-isolation-arithmetic162k.json')
for peer in iso['peer_original_initial_briefs']:
    assert sha((p / peer['brief']).read_bytes()) == peer['brief_sha256']
selection = load(o / 'private/catalogue-selection.json')
with (p / 'sources/CONTENTS.md').open('rb') as f:
    f.seek(selection['start']); selected = f.read(selection['end'] - selection['start'])
assert sha(selected) == selection['sha256'] and selected == (o / 'private/catalogue-075.md').read_bytes()
for i, x in enumerate(base['tasks']):
    if i != 667:
        assert tasks['tasks'][i] == x
for k, v in base.items():
    if k not in ['tasks', 'last_parent_progress', 'current_work_snapshot']:
        assert tasks[k] == v
append = ('\n\n### Arithmetic162j continuation archived; distinct Arithmetic162k dispatched\n\n' + note + '\n\nThe continuation completed its previously unfinished canonical reading and the named operative primary/recursive comparisons. Partial companion sections,deep unread transitive proofs and authenticated-only/unrendered PDFs remain explicit. Parent read the complete research derivation and records; no independent canonical/primary review grade assigned. All106 payload files (5,476,891 bytes), three anchors and35 canonical bindings matched;23 primary file bindings and two original-history spans rechecked. All114 completed-root files retained bytes/modes. Artifact checks are not mathematical gates.\n\nThe new calculation pays the horizontal endpoint time factor exactlylambda^4 under explicit state/velocity contracts. Actual same-mass preparation,common-palette domination,normal labels,original-prior recovery and overlap still require the subpower combined coefficient r^4 F^(-2/s) A^(-3-2/s)/(L^3 D),or a proved compensating gain. Full4D L4 maximal scope remains UNCHANGED_UNPROVED; no restricted replacement frozen and no count. Prior sparse-time/plane-direction/Falconer/closedPASS-TECHNICAL scopes retain their dispositions.\n\nParent assessment: frontier/campaigns/2026-10-14/arithmetic-r162j-continuation-r1-parent/assessment.md. Separate Source075 discovery uses ONLY catalogue[127638,128445),one actual build/main.tex wrapper and17 canonical blobs. Parent source access is metadata only; complete operative/primary/original-history reading precedes extended deductions. All source proof operations and the full ordinary symmetric L log L convergence theorem are stipulated true and paid. Foreign recorded initial wildcard guards cover the new namespace prospectively; no peer liveness/findings/body query or steering. Child running was observed only at successful dispatch. Publication and downstream work remain stopped.\n').encode()
assert head == git('rev-parse', 'HEAD').decode().strip()
assert tpath.read_bytes() == old_t and jpath.read_bytes() == old_j
write(o / 'coordination-rebase.json', {'initial_head': baseline['head'], 'integration_head': head,
    'rebased': head != baseline['head'], 'initial_tasks': baseline['taskCount'],
    'integration_tasks': len(base['tasks']), 'completed_task_index': 667,
    'new_task_index': new_index, 'preserved_other_tasks': len(base['tasks']) - 1,
    'foreign_liveness_not_queried': True})
write(tpath, tasks)
jpath.write_bytes(old_j + append)
assert jpath.read_bytes().startswith(old_j)
write(o / 'private/journal-append.json', {'prior_bytes': len(old_j), 'prior_sha256': sha(old_j), 'append_bytes': len(append), 'append_sha256': sha(append)})
stage = [tpath, jpath, brief_path, a / 'REPORT.md', a / 'packet/FINAL.md',
         a / 'packet/PREFREEZE.md', a / 'packet/VERIFY.py', a / 'seal/ANCHORS.json']
stage += [o / x for x in ['integration-baseline.json', 'task-status.json', 'capabilities.json',
    'verification.json', 'assessment.md', 'intake.json', 'verify-intake.py',
    'prospective-isolation-arithmetic162k.json', 'prepare-brief.py', 'brief-preparation.json',
    'arithmetic-r162k-dispatch.json', 'manage.py', 'coordination-rebase.json', 'integration-guard.json']]
relative = [f.relative_to(p).as_posix() for f in stage]
assert all('/private/' not in x and not x.endswith('MANIFEST.json') and '/controls/' not in x for x in relative)
write(o / 'integration-guard.json', {'baseline_head': head, 'completed_task_index': 667,
    'new_task_index': new_index, 'old_tasks_preserved_except667': True,
    'other_top_level_preserved_except_progress_snapshot': True, 'journal_prefix_preserved': True,
    'completed_root114files_unchanged': True, 'artifact_verification': '106 files/35 canonical blobs/three anchors matched; no mathematical gate',
    'author_complete_canonical_own_reading_reported': 1019669, 'bounded_transitive_limits_preserved': True,
    'old_literal_guards_retained': len(guards), 'new_literal_guards': prep['new_literal_guards'],
    'standing5570bytes_unchanged': True, 'old_full_targets_and_dispositions_unchanged': True,
    'new_family': 'DISTINCT Source075; complete operative reading before extended deductions',
    'new_runtime': 'codex/gpt-6-astra/high/default; actual running dispatch; no pending child/question/approval',
    'prospective_foreign_initial_guards': len(iso['peer_original_initial_briefs']),
    'foreign_liveness_not_queried': True, 'count': 19, 'remaining': 1, 'latestAcceptance': 'R041',
    'publication': 'STOPPED', 'stage_allowlist': relative, 'protected_excluded': baseline['protected']})
assert author_snapshot() == load(o / 'private/root-before.json')
assert head == git('rev-parse', 'HEAD').decode().strip()
subprocess.run(['git', 'add', '--', *relative], check=True)
assert set(git('diff', '--cached', '--name-only').decode().splitlines()) == {'openai-proof-research/' + x for x in relative}
for rel in relative:
    assert git('show', ':openai-proof-research/' + rel) == (p / rel).read_bytes()
print(json.dumps({'status': 'INTEGRATED_AND_STAGED', 'head': head, 'new_task_index': new_index,
                  'files': len(relative), 'count': 19, 'remaining': 1}, indent=2))
