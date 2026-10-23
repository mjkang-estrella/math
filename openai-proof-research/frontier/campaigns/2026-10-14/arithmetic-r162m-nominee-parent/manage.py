#!/usr/bin/env python3
"""Integrate one immutable nominee and its two independent review dispatches."""
from pathlib import Path
import copy
import datetime
import hashlib
import json
import re
import subprocess

p = Path.cwd()
b = p / 'frontier/campaigns/2026-10-14'
o = b / 'arithmetic-r162m-nominee-parent'
a = b / 'fresh-arithmetic-discovery-r162m'
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
assert (o / 'capabilities.json').is_file() and (o / 'capabilities-at-dispatch.json').is_file()
assert author_snapshot() == load(o / 'private/root-before.json')
for rel, digest in baseline['protected'].items():
    assert sha((p / rel).read_bytes()) == digest
assert not git('diff', '--cached', '--name-only')
head = git('rev-parse', 'HEAD').decode().strip()
old_t = git('show', head + ':openai-proof-research/' + tpath.relative_to(p).as_posix())
old_j = git('show', head + ':openai-proof-research/' + jpath.relative_to(p).as_posix())
assert tpath.read_bytes() == old_t and jpath.read_bytes() == old_j, 'Other-owner coordination is uncommitted; do not overwrite.'
base = json.loads(old_t)
tasks = copy.deepcopy(base)
assert (tasks['newAccepted'], tasks['target'], tasks['remaining'], tasks['latestAcceptance']) == (19, 20, 1, 'R041')
terminal = load(o / 'task-status.json')['structuredContent']
assert terminal['status'] == 'completed' and terminal['workState'] == 'result_available'
assert [i for i, x in enumerate(tasks['tasks']) if x.get('taskId') == terminal['taskId']] == [671]
assert not terminal['hasPendingChildRuns'] and not terminal['hasPendingQuestion'] and terminal['pendingApproval'] is None
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
verification = load(o / 'verification.json')
frozen_sha, proof_sha = verification['frozen_sha256'], verification['proof_sha256']
assert sha((a / 'packet/FROZEN-THEOREM.md').read_bytes()) == frozen_sha
assert sha((a / 'packet/AUTHOR-PROOF.md').read_bytes()) == proof_sha
tasks['tasks'][671].update(terminal)
tasks['tasks'][671].update({'observed_utc': now,
    'parent_intake': 'arithmetic-r162m-nominee-parent/intake.json',
    'parent_disposition': 'FULL_AUTHOR_PROOF_NOMINEE_AWAITING_INDEPENDENT_REVIEWS',
    'frozen': 'fresh-arithmetic-discovery-r162m/packet/FROZEN-THEOREM.md',
    'frozen_sha256': frozen_sha, 'author_proof': 'fresh-arithmetic-discovery-r162m/packet/AUTHOR-PROOF.md',
    'author_proof_sha256': proof_sha, 'correctness_gate': None, 'contribution_gate': None,
    'accepted': False, 'count_change': 0,
    'status_provenance': 'Single notified terminal task_status receipt; no pending child/question/approval.'})
preparations = {x['review_role']: x for x in load(o / 'review-preparation.json')}
original = (b / 'expanded-target-2026-10-17/fresh-arithmetic-r162m-brief.txt').read_bytes()
old_guards = set(re.findall(rb'\*[^\s,;()]*\*', original))
marker = b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
reviews, dispatches, brief_paths = {}, [], []
for role in ['proof', 'contribution']:
    d = load(o / (role + '-dispatch.json'))['structuredContent']
    args = load(o / 'private' / (role + '-submitted.json'))
    prep = preparations[role]
    assert d['status'] == 'running' and d['workState'] == 'working'
    assert (d['providerInstanceId'], d['model']) == ('codex', 'gpt-6-astra')
    assert {x['id']: x['value'] for x in d['options']} == {'reasoningEffort': 'high', 'serviceTier': 'default'}
    assert not d['hasPendingChildRuns'] and not d['hasPendingQuestion'] and d['pendingApproval'] is None
    assert not any(x.get('taskId') == d['taskId'] or x.get('clientRequestId') == args['clientRequestId'] for x in tasks['tasks'])
    brief_path = p / prep['brief']
    brief = brief_path.read_bytes()
    assert args['task'].encode() == brief and len(brief) == prep['brief_bytes'] and sha(brief) == prep['brief_sha256']
    assert brief.endswith(original) and brief.split(marker, 1)[1] == original.split(marker, 1)[1]
    assert len(brief.split(marker, 1)[1]) == 5570
    assert old_guards <= set(re.findall(rb'\*[^\s,;()]*\*', brief))
    assert (a / 'packet/FROZEN-THEOREM.md').read_bytes() in brief and (a / 'packet/AUTHOR-PROOF.md').read_bytes() in brief
    entry = copy.deepcopy(d)
    entry.update({'observed_utc': now, 'target': args['target'], 'role': 'review', 'review_gate': 'correctness' if role == 'proof' else 'substantial_contribution_conditional_on_full_correctness',
        'title': args['title'], 'output': prep['root'] + '/', 'brief': prep['brief'],
        'brief_sha256': prep['brief_sha256'], 'brief_bytes': prep['brief_bytes'],
        'original_author_task_index': 671, 'candidate': 'Arithmetic162m',
        'frozen': 'fresh-arithmetic-discovery-r162m/packet/FROZEN-THEOREM.md', 'frozen_sha256': frozen_sha,
        'author_proof': 'fresh-arithmetic-discovery-r162m/packet/AUTHOR-PROOF.md', 'author_proof_sha256': proof_sha,
        'entire_frozen_scope_unchanged': True, 'initial_mutual_review_exclusions': True,
        'parent_count_at_dispatch': 19, 'accepted': False, 'count_change': 0, 'publication': 'STOPPED',
        'dispatch_receipt': 'arithmetic-r162m-nominee-parent/' + role + '-dispatch.json',
        'prospective_isolation': 'arithmetic-r162m-nominee-parent/prospective-review-isolation.json',
        'clientRequestId': args['clientRequestId'], 'round': 1,
        'parent_thread': '6742db91-d35c-44d0-a762-e5d9232f5177',
        'status_provenance': 'Actual successful delegate_task response; running at dispatch, not a later liveness poll.'})
    idx = len(tasks['tasks'])
    tasks['tasks'].append(entry)
    reviews[role] = {'task_index': idx, 'taskId': d['taskId'], 'root': prep['root']}
    dispatches.append(d)
    brief_paths.append(brief_path)
note = f'Arithmetic162m(idx671) delivered FULL AUTHOR-PROOF NOMINEE: all stipulated surfaces and finitep>3,all normalized rough complexLp extremizing sequences strongly compact modulo modulations,with norm attainment and qualitative stability. Immutable whole theorem/proof bound; no parent mathematical gate/count. Exact96-file/29-canonical checks passed; all104 author-root files unchanged. Independent full correctness(idx{reviews["proof"]["task_index"]}) and separate full substantial-contribution conditional on correctness(idx{reviews["contribution"]["task_index"]}) reviews dispatched with Astra high/default,mutually excluded from INITIAL briefs. Entire original assignment,frozen theorem and proof included verbatim. No downstream work. Other-owner tasks and all older scopes/dispositions preserved without live status/body inspection or steering. Campaign19/20,latestR041,one remains; publication STOPPED.'
tasks['last_parent_progress'] = note
s = tasks['current_work_snapshot']
s.update({'observed_utc': now, 'note': note, 'accepted_count': 19, 'remaining': 1, 'publication': 'STOPPED'})
s['t3_current_confirmed_running'] = [x for x in s.get('t3_current_confirmed_running', []) if x != terminal['taskId']]
s['t3_current_confirmed_running'].extend(d['taskId'] for d in dispatches)
s.setdefault('t3_dispatch_observations', []).extend({'observed_utc': now, **d} for d in dispatches)
s['arithmetic_r162m_nominee'] = {'task_index': 671, 'status': 'AWAITING_TWO_INDEPENDENT_FULL_SCOPE_REVIEWS',
    'intake': 'arithmetic-r162m-nominee-parent/intake.json', 'frozen_sha256': frozen_sha,
    'proof_sha256': proof_sha, 'correctness_gate': None, 'contribution_gate': None,
    'reviews': reviews, 'accepted': False, 'count_change': 0}
iso = load(o / 'prospective-review-isolation.json')
for peer in iso['peer_original_initial_briefs']:
    assert sha((p / peer['brief']).read_bytes()) == peer['brief_sha256']
for i, x in enumerate(base['tasks']):
    if i != 671:
        assert tasks['tasks'][i] == x
for k, v in base.items():
    if k not in ['tasks', 'last_parent_progress', 'current_work_snapshot']:
        assert tasks[k] == v
append = ('\n\n### Arithmetic162m full author nominee; separate full reviews dispatched\n\n' + note + '\n\nThe entire frozen theorem covers every nonempty compact smooth embedded definite-curvature surface inR3,including smooth boundary,every finitep>3,and every normalized complexLp extremizing sequence. It asserts strong subsequence convergence modulo the exact modulations,norm attainment and qualitative stability relative to the entire extremizer set. No endpoint,classification,rate,uniform-surface constant or regular-input restriction. Frozen1645bytes SHA256' + frozen_sha + ';author proof17147bytes SHA256' + proof_sha + '. Author reports no gap;this is not independent validation.\n\nThe proposed bridge combines the actual paid L3->Lq interface belowp,high-exponent Hilbert extraction,fixed-J output splitting and remainder control,local weighted square mass,diagonal equality,analytic overlap and complex plus/minus strictness. Both independent reviews must reconstruct the entire compatible argument and exact source/primary scope. Correctness and conditional contribution are separate;no gate/count is adopted. Neither reviewer may inspect the other role or alter frozen inputs. Original research assignment,whole theorem and proof are in both initial prompts.\n\nAll96 payload files (3,448,737 bytes),three detached anchors and29 canonical bindings matched. Ten primary file bindings,five original-history whole/span pairs and four completed-original hashes rechecked;seven saved copied controls matched. All104 author-root files retained bytes/modes. Author reports full27-object non-PDF canonical reading470177bytes,with two PDFs authentication-only and explicit transitive-primary gaps. The parent read the full author proof and records,not the canonical/primary proofs. Artifact checks are not mathematical gates.\n\nParent assessment: frontier/campaigns/2026-10-14/arithmetic-r162m-nominee-parent/assessment.md. Exact original-history metadata binds whole originals plus semantic spans;the parent stopped on an initial hash-scope assumption,then verified both scopes separately without author changes. A saved in-memory capability receipt was unavailable after user steering;no delegate call had occurred,a fresh live capability receipt was saved,and both unique requests then dispatched once. Foreign original initial guards were checked before both review namespaces existed;no fresh liveness/body/findings query. Every old target and wholePASS/TECHNICAL zero-count disposition remains unchanged. Publication and downstream work stopped.\n').encode()
assert head == git('rev-parse', 'HEAD').decode().strip()
assert tpath.read_bytes() == old_t and jpath.read_bytes() == old_j
write(o / 'coordination-rebase.json', {'initial_head': baseline['head'], 'integration_head': head,
    'rebased': head != baseline['head'], 'initial_tasks': baseline['taskCount'],
    'integration_tasks': len(base['tasks']), 'author_task_index': 671, 'reviews': reviews,
    'preserved_other_tasks': len(base['tasks']) - 1, 'foreign_liveness_not_queried': True})
write(tpath, tasks)
jpath.write_bytes(old_j + append)
assert jpath.read_bytes().startswith(old_j)
write(o / 'private/journal-append.json', {'prior_bytes': len(old_j), 'prior_sha256': sha(old_j),
    'append_bytes': len(append), 'append_sha256': sha(append)})
stage = [tpath, jpath, *brief_paths, a / 'REPORT.md', a / 'ANCHORS.json', a / 'packet/FINAL.md',
    a / 'packet/FROZEN-THEOREM.md', a / 'packet/AUTHOR-PROOF.md', a / 'packet/verify_packet.py']
stage += [o / x for x in ['integration-baseline.json', 'task-status.json', 'capabilities.json',
    'capabilities-at-dispatch.json', 'verification.json', 'assessment.md', 'intake.json',
    'verify-intake.py', 'prospective-review-isolation.json', 'prepare-reviews.py',
    'review-preparation.json', 'proof-dispatch.json', 'contribution-dispatch.json',
    'manage.py', 'coordination-rebase.json', 'integration-guard.json']]
relative = [f.relative_to(p).as_posix() for f in stage]
assert all('/private/' not in x and not x.endswith('MANIFEST.json') and '/controls/' not in x for x in relative)
write(o / 'integration-guard.json', {'baseline_head': head, 'author_task_index': 671,
    'review_tasks': reviews, 'old_tasks_preserved_except671': True,
    'other_top_level_preserved_except_progress_snapshot': True, 'journal_prefix_preserved': True,
    'author_root104files_unchanged': True, 'frozen_sha256': frozen_sha, 'proof_sha256': proof_sha,
    'artifact_checks': '96 files/29 canonical blobs/three anchors matched; not mathematical gates',
    'old_guards_retained': len(old_guards), 'standing5570bytes_unchanged': True,
    'original_assignment_frozen_and_proof_verbatim_in_both_reviews': True,
    'initial_mutual_review_exclusions': True, 'foreign_initial_guards_before_review_roots': True,
    'new_runtimes': 'both codex/gpt-6-astra/high/default; actual running dispatches; no pending child/question/approval',
    'correctness_gate': None, 'contribution_gate': None, 'accepted': False, 'count_change': 0,
    'count': 19, 'remaining': 1, 'latestAcceptance': 'R041', 'publication': 'STOPPED',
    'no_downstream_work': True, 'stage_allowlist': relative, 'protected_excluded': baseline['protected']})
assert author_snapshot() == load(o / 'private/root-before.json')
assert head == git('rev-parse', 'HEAD').decode().strip()
subprocess.run(['git', 'add', '--', *relative], check=True)
assert set(git('diff', '--cached', '--name-only').decode().splitlines()) == {'openai-proof-research/' + x for x in relative}
for rel in relative:
    assert git('show', ':openai-proof-research/' + rel) == (p / rel).read_bytes()
print(json.dumps({'status': 'INTEGRATED_AND_STAGED', 'head': head, 'reviews': reviews,
    'files': len(relative), 'count': 19, 'remaining': 1}, indent=2))
