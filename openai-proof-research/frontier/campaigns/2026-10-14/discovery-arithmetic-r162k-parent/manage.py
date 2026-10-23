#!/usr/bin/env python3
"""Archive notified r162k and record exactly one distinct r162l dispatch."""
from pathlib import Path
import copy
import datetime
import hashlib
import json
import re
import subprocess

p = Path.cwd()
b = p / 'frontier/campaigns/2026-10-14'
o = b / 'discovery-arithmetic-r162k-parent'
a = b / 'fresh-arithmetic-discovery-r162k'
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
assert tpath.read_bytes() == old_t and jpath.read_bytes() == old_j, 'Uncommitted other-owner coordination; do not overwrite.'
base = json.loads(old_t)
tasks = copy.deepcopy(base)
assert (tasks['newAccepted'], tasks['target'], tasks['remaining'], tasks['latestAcceptance']) == (19, 20, 1, 'R041')
terminal = load(o / 'task-status.json')['structuredContent']
dispatch = load(o / 'arithmetic-r162l-dispatch.json')['structuredContent']
args = load(o / 'private/submitted-prompt.json')
assert terminal['status'] == 'completed' and terminal['workState'] == 'result_available'
assert dispatch['status'] == 'running' and dispatch['workState'] == 'working'
for d in [terminal, dispatch]:
    assert (d['providerInstanceId'], d['model']) == ('codex', 'gpt-6-astra')
    assert {x['id']: x['value'] for x in d['options']} == {'reasoningEffort': 'high', 'serviceTier': 'default'}
    assert not d['hasPendingChildRuns'] and not d['hasPendingQuestion'] and d['pendingApproval'] is None
assert [i for i, x in enumerate(tasks['tasks']) if x.get('taskId') == terminal['taskId']] == [669]
assert not any(x.get('taskId') == dispatch['taskId'] or x.get('clientRequestId') == args['clientRequestId'] for x in tasks['tasks'])
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
tasks['tasks'][669].update(terminal)
tasks['tasks'][669].update({'observed_utc': now,
    'parent_intake': 'discovery-arithmetic-r162k-parent/intake.json',
    'parent_disposition': 'PREFREEZE_NO_NOMINEE_ARCHIVED', 'accepted': False, 'count_change': 0,
    'status_provenance': 'Single actual notified terminal task_status response; no pending child/question/approval.'})
brief_path = b / 'expanded-target-2026-10-17/fresh-arithmetic-r162l-brief.txt'
brief, prep = brief_path.read_bytes(), load(o / 'brief-preparation.json')
assert args['task'].encode() == brief and len(brief) == prep['bytes'] and sha(brief) == prep['sha256']
new = copy.deepcopy(dispatch)
new.update({'observed_utc': now, 'target': args['target'], 'role': args['role'], 'title': args['title'],
    'output': 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162l/',
    'brief': brief_path.relative_to(p).as_posix(), 'brief_sha256': sha(brief), 'brief_bytes': len(brief),
    'source_family_navigation': 'DISTINCT Source076; exact catalogue[128445,130739), three canonical folders,41 descendants/35 blobs; actual build/main.tex wrappers. Parent metadata navigation only; complete operative reading before extended deductions.',
    'round_namespace': 'NEW DISTINCT Source076 inside previously excluded arithmetic162 namespace; no retry/restriction of weighted one-log endpoint, full4D maximal or other old targets.',
    'parent_count_at_dispatch': 19, 'accepted': False, 'count_change': 0, 'publication': 'STOPPED',
    'dispatch_receipt': 'discovery-arithmetic-r162k-parent/arithmetic-r162l-dispatch.json',
    'prospective_isolation': 'discovery-arithmetic-r162k-parent/prospective-isolation-arithmetic162l.json',
    'clientRequestId': args['clientRequestId'], 'round': 1,
    'parent_thread': '6742db91-d35c-44d0-a762-e5d9232f5177',
    'status_provenance': 'Actual successful delegate_task response; running at dispatch, not a later liveness poll.'})
new_index = len(tasks['tasks'])
tasks['tasks'].append(new)
note = f'Arithmetic162k(idx669) completed PREFREEZE/no nominee. Full weighted A log^2(e+B) endpoint and refined bounded-block estimate are paid; full A log(e+B) target remains UNCHANGED_UNPROVED at compatible weighted live/Fisher plus predictable drift or stronger endpoint summation. All16 canonical non-PDF files257892bytes own-read as recorded; primary/transitive limits retained. Exact57-member/17-canonical checks passed; all64 completed-root files unchanged; no grade/count. Arithmetic162l(idx{new_index}, DISTINCT Source076 real-Littlewood ultraflatness family) dispatched with Astra high/default in the already excluded162 namespace. All old scopes/zero-count closures and foreign-owner tasks preserved without live body/status inspection or steering. Campaign19/20,latestR041,one remains; publication STOPPED.'
tasks['last_parent_progress'] = note
s = tasks['current_work_snapshot']
s.update({'observed_utc': now, 'note': note, 'accepted_count': 19, 'remaining': 1, 'publication': 'STOPPED'})
s['t3_current_confirmed_running'] = [x for x in s.get('t3_current_confirmed_running', []) if x != terminal['taskId']]
s['t3_current_confirmed_running'].append(dispatch['taskId'])
s.setdefault('t3_dispatch_observations', []).append({'observed_utc': now, **dispatch})
s['arithmetic_r162k_archive'] = {'task_index': 669, 'status': 'PREFREEZE_NO_NOMINEE_ARCHIVED',
    'intake': 'discovery-arithmetic-r162k-parent/intake.json', 'count_change': 0,
    'full_target': 'UNCHANGED_UNPROVED_WEIGHTED_ONE_LOG_ENDPOINT'}
previous = (b / 'expanded-target-2026-10-17/fresh-arithmetic-r162k-brief.txt').read_bytes()
guards = set(re.findall(rb'\*[^\s,;()]*\*', previous))
assert guards <= set(re.findall(rb'\*[^\s,;()]*\*', brief))
marker = b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
assert brief.split(marker, 1)[1] == previous.split(marker, 1)[1]
assert len(brief.split(marker, 1)[1]) == 5570
iso = load(o / 'prospective-isolation-arithmetic162l.json')
for peer in iso['peer_original_initial_briefs']:
    assert sha((p / peer['brief']).read_bytes()) == peer['brief_sha256']
sel = load(o / 'private/catalogue-selection.json')
with (p / 'sources/CONTENTS.md').open('rb') as f:
    f.seek(sel['start']); selected = f.read(sel['end'] - sel['start'])
assert sha(selected) == sel['sha256'] and selected == (o / 'private/catalogue-076.md').read_bytes()
for i, x in enumerate(base['tasks']):
    if i != 669:
        assert tasks['tasks'][i] == x
for k, v in base.items():
    if k not in ['tasks', 'last_parent_progress', 'current_work_snapshot']:
        assert tasks[k] == v
append = ('\n\n### Arithmetic162k archived; distinct Arithmetic162l dispatched\n\n' + note + '\n\nThe actual source/primary reduction pays the full squared-log weighted modular estimate,including finite-rank repair of the maximal-principle interface,local sparse compatibility and Hu Orlicz-average replacement. The one-log full-input target is not frozen. Compatible weighted live/Fisher correlation and predictable drift remain unpaid; failed mean replacement,exceptional-set transfer,threshold allocation and generic output-entropy repairs neither refute the target nor establish sharpness.\n\nAll57 payload members (3,327,242 bytes),three anchors and17 pinned canonical bindings matched. Four original-history spans,four completed-original copies,four primary archives,five extracted primary files and the Hu PDF rechecked;three saved tiny copied controls matched. All64 completed-root files retained bytes/modes. Author reports all16 canonical non-PDF files257892bytes completely read; compiled PDF authentication-only. Primary/transitive,version,clipping/gzip recovery and isolation limits remain disclosed. Artifact checks assign no mathematical gate.\n\nParent assessment: frontier/campaigns/2026-10-14/discovery-arithmetic-r162k-parent/assessment.md. Separate Source076 uses ONLY catalogue[128445,130739),three confirmed folders and35 canonical blobs. Parent read metadata only. All upstream source proof operations and the full ultraflat/all-integer-length/merit-factor conclusions are stipulated true and paid. Complete actual canonical/primary/original-history reading precedes extended deductions. All old targets and closedPASS/TECHNICAL zero-count dispositions preserved. Foreign original initial guards covered the new namespace before creation; no live findings/body/status query or steering. Child running observed only at actual successful dispatch. Publication/downstream work remain stopped.\n').encode()
assert head == git('rev-parse', 'HEAD').decode().strip()
assert tpath.read_bytes() == old_t and jpath.read_bytes() == old_j
write(o / 'coordination-rebase.json', {'initial_head': baseline['head'], 'integration_head': head,
    'rebased': head != baseline['head'], 'initial_tasks': baseline['taskCount'],
    'integration_tasks': len(base['tasks']), 'completed_task_index': 669, 'new_task_index': new_index,
    'preserved_other_tasks': len(base['tasks']) - 1, 'foreign_liveness_not_queried': True})
write(tpath, tasks)
jpath.write_bytes(old_j + append)
assert jpath.read_bytes().startswith(old_j)
write(o / 'private/journal-append.json', {'prior_bytes': len(old_j), 'prior_sha256': sha(old_j),
    'append_bytes': len(append), 'append_sha256': sha(append)})
stage = [tpath, jpath, brief_path, a / 'REPORT.md', a / 'packet/FINAL.md',
         a / 'packet/verify_packet.py', a / 'ANCHORS.json']
stage += [o / x for x in ['integration-baseline.json', 'task-status.json', 'capabilities.json',
    'verification.json', 'assessment.md', 'intake.json', 'verify-intake.py',
    'prospective-isolation-arithmetic162l.json', 'prepare-brief.py', 'brief-preparation.json',
    'arithmetic-r162l-dispatch.json', 'manage.py', 'coordination-rebase.json', 'integration-guard.json']]
relative = [f.relative_to(p).as_posix() for f in stage]
assert all('/private/' not in x and not x.endswith('MANIFEST.json') and '/controls/' not in x for x in relative)
write(o / 'integration-guard.json', {'baseline_head': head, 'completed_task_index': 669,
    'new_task_index': new_index, 'old_tasks_preserved_except669': True,
    'other_top_level_preserved_except_progress_snapshot': True, 'journal_prefix_preserved': True,
    'completed_root64files_unchanged': True, 'artifact_checks': '57 members/17 canonical blobs/three anchors matched; not mathematical gates',
    'author_complete_canonical_non_pdf_reading_reported': 257892, 'primary_transitive_limits_retained': True,
    'old_literal_guards_retained': len(guards), 'new_literal_guards': prep['new_literal_guards'],
    'standing5570bytes_unchanged': True, 'old_full_targets_and_dispositions_unchanged': True,
    'new_family': 'DISTINCT Source076; complete actual operative reading before extended deductions',
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
