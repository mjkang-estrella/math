#!/usr/bin/env python3
"""Adopt one independent full correctness gate without consulting its peer."""
from pathlib import Path
import copy
import datetime
import hashlib
import json
import subprocess

p = Path.cwd()
b = p / 'frontier/campaigns/2026-10-14'
o = b / 'arithmetic-r162m-proof-r1-parent'
r = b / 'arithmetic-r162m-proof-r1'
a = b / 'fresh-arithmetic-discovery-r162m'
tpath, jpath = b / 'tasks.json', p / 'frontier/NEW-TEN-2026-10-14.md'
git = lambda *args: subprocess.check_output(['git', *args])
sha = lambda d: hashlib.sha256(d).hexdigest()
load = lambda f: json.loads(f.read_bytes())

def write(f, value):
    f.write_text(json.dumps(value, indent=2) + '\n')

def snapshot(root):
    return {f.relative_to(root).as_posix(): {'bytes': f.stat().st_size,
        'mode': f.stat().st_mode, 'sha256': sha(f.read_bytes())}
        for f in root.rglob('*') if f.is_file()}

baseline = load(o / 'integration-baseline.json')
assert snapshot(a) == load(o / 'private/author-root-before.json')
assert snapshot(r) == load(o / 'private/review-root-before.json')
for rel, digest in baseline['protected'].items():
    assert sha((p / rel).read_bytes()) == digest
assert not git('diff', '--cached', '--name-only')
head = git('rev-parse', 'HEAD').decode().strip()
old_t = git('show', head + ':openai-proof-research/' + tpath.relative_to(p).as_posix())
old_j = git('show', head + ':openai-proof-research/' + jpath.relative_to(p).as_posix())
assert old_t == tpath.read_bytes() and old_j == jpath.read_bytes(), 'Uncommitted other-owner coordination; do not overwrite.'
base = json.loads(old_t)
tasks = copy.deepcopy(base)
assert (tasks['newAccepted'], tasks['target'], tasks['remaining'], tasks['latestAcceptance']) == (19, 20, 1, 'R041')
terminal = load(o / 'task-status.json')['structuredContent']
assert terminal['status'] == 'completed' and terminal['workState'] == 'result_available'
assert (terminal['providerInstanceId'], terminal['model']) == ('codex', 'gpt-6-astra')
assert {x['id']: x['value'] for x in terminal['options']} == {'reasoningEffort': 'high', 'serviceTier': 'default'}
assert not terminal['hasPendingChildRuns'] and not terminal['hasPendingQuestion'] and terminal['pendingApproval'] is None
assert [i for i, x in enumerate(tasks['tasks']) if x.get('taskId') == terminal['taskId']] == [672]
assert tasks['tasks'][672]['original_author_task_index'] == 671
v = load(o / 'verification.json')
assert tasks['tasks'][671]['frozen_sha256'] == v['frozen_sha256']
assert tasks['tasks'][671]['author_proof_sha256'] == v['proof_sha256']
assert tasks['tasks'][671]['contribution_gate'] is None
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
gate = {'verdict': 'PASS', 'scope': 'entire unchanged frozen theorem and author proof',
    'relative_to_stipulated_upstream_truth': 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
    'review_task_index': 672, 'review_taskId': terminal['taskId'],
    'parent_intake': 'arithmetic-r162m-proof-r1-parent/intake.json',
    'frozen_sha256': v['frozen_sha256'], 'proof_sha256': v['proof_sha256'],
    'necessary_author_corrections': [], 'essential_unresolved_correctness_obligations': [],
    'adopted_utc': now}
tasks['tasks'][672].update(terminal)
tasks['tasks'][672].update({'observed_utc': now,
    'status_provenance': 'Single notified terminal task_status response; no pending child/question/approval.',
    'parent_disposition': 'FULL_SCOPE_CORRECTNESS_PASS_ADOPTED', 'parent_gate': gate,
    'parent_intake': 'arithmetic-r162m-proof-r1-parent/intake.json',
    'accepted': False, 'count_change': 0})
tasks['tasks'][671].update({'correctness_gate': gate,
    'correctness_parent_intake': 'arithmetic-r162m-proof-r1-parent/intake.json',
    'parent_disposition': 'FULL_AUTHOR_PROOF_NOMINEE_CORRECTNESS_PASS_AWAITING_CONTRIBUTION',
    'accepted': False, 'count_change': 0})
note = 'Arithmetic162m full unchanged correctness PASS(idx672) adopted for author nominee(idx671),relative to stipulated upstream truth. Every complexLp sequence,finitep>3,boundary surface,countable extraction,modulation,attainment and qualitative-stability quantifier covered; no necessary repair or essential correctness gap. Exact67-file/20-directory review verification,29 canonical bindings and21 immutable author-input pre/post/current checks passed; all104 author-root and71 review-root files unchanged. Contribution remains unassigned; its already dispatched task is not queried or inspected. No acceptance,count change,new task or downstream work. All other-owner tasks and old scopes/dispositions preserved. Campaign19/20,latestR041,one remains; publication STOPPED.'
tasks['last_parent_progress'] = note
s = tasks['current_work_snapshot']
s.update({'observed_utc': now, 'note': note, 'accepted_count': 19, 'remaining': 1, 'publication': 'STOPPED'})
s['t3_current_confirmed_running'] = [x for x in s.get('t3_current_confirmed_running', []) if x != terminal['taskId']]
nominee = s['arithmetic_r162m_nominee']
assert nominee['contribution_gate'] is None
nominee.update({'status': 'CORRECTNESS_PASS_AWAITING_FULL_SCOPE_CONTRIBUTION',
    'correctness_gate': gate, 'accepted': False, 'count_change': 0})
s['arithmetic_r162m_correctness_adoption'] = gate
for i, x in enumerate(base['tasks']):
    if i not in [671, 672]:
        assert tasks['tasks'][i] == x
assert tasks['tasks'][673] == base['tasks'][673]
for k, value in base.items():
    if k not in ['tasks', 'last_parent_progress', 'current_work_snapshot']:
        assert tasks[k] == value
iso = load(o / 'prospective-parent-isolation.json')
for peer in iso['foreign_original_initial_briefs']:
    assert sha((p / peer['brief']).read_bytes()) == peer['brief_sha256']
append = ('\n\n### Arithmetic162m full correctness PASS adopted; contribution unassigned\n\n' + note + '\n\nThe entire independent derivation reconstructs the actual L3->Lq source interface,rough boundary chart transfer,all exponent regimes including3<p<4,Hilbert extraction with original-sequence weakLp profiles,one increasing diagonal subsequence,fixed-J splitting and uniform-in-J OUTPUT remainder. Weighted local square mass and exact equality force disjoint profile supports;analytic overlap and strict complex plus/minus convexity exclude two nonzero profiles. Correct signs,strongLp convergence,attainment and qualitative stability relative to the entire extremizer set follow. No altered hypotheses,restricted PASS,rate,classification,endpoint or surface-uniform claim.\n\nFrozen theorem SHA256' + v['frozen_sha256'] + ';author proof SHA256' + v['proof_sha256'] + '. All21 permitted author inputs preserve bytes/hashes/modes;all104 author-root and71 review-root files unchanged. Review67 files (2,643,823 bytes),20directories,three detached anchors,29 canonical blobs,eight primary bindings and five original-history spans matched;three saved copied controls matched. These are artifact checks,not the mathematical basis of PASS. Full canonical text470177bytes read by reviewer;selected primary proofs and transitive/unrendered limits disclosed. Parent read the full independent derivation and limits,not the canonical/primary proofs.\n\nParent assessment: frontier/campaigns/2026-10-14/arithmetic-r162m-proof-r1-parent/assessment.md. Contribution task673 remains exactly as recorded,without status,body,findings or activity inspection. No contribution grade,acceptance,count,new task or downstream work is assigned. Foreign committed changes and every prior scope/disposition are preserved. Publication stopped.\n').encode()
assert head == git('rev-parse', 'HEAD').decode().strip()
assert old_t == tpath.read_bytes() and old_j == jpath.read_bytes()
write(o / 'coordination-rebase.json', {'initial_head': baseline['head'], 'integration_head': head,
    'rebased': head != baseline['head'], 'initial_tasks': baseline['taskCount'],
    'integration_tasks': len(base['tasks']), 'changed_task_indices': [671, 672],
    'preserved_other_tasks': len(base['tasks']) - 2, 'contribution_task673_unchanged': True,
    'contribution_and_foreign_liveness_not_queried': True})
write(tpath, tasks)
jpath.write_bytes(old_j + append)
assert jpath.read_bytes().startswith(old_j)
write(o / 'private/journal-append.json', {'prior_bytes': len(old_j), 'prior_sha256': sha(old_j),
    'append_bytes': len(append), 'append_sha256': sha(append)})
stage = [tpath, jpath, r / 'REPORT.md', r / 'ANCHORS.json', r / 'packet/FINAL.md',
    r / 'packet/REVIEW.md', r / 'packet/verify_packet.py']
stage += [o / x for x in ['integration-baseline.json', 'task-status.json', 'verification.json',
    'assessment.md', 'intake.json', 'verify-intake.py', 'prospective-parent-isolation.json',
    'manage.py', 'coordination-rebase.json', 'integration-guard.json']]
relative = [f.relative_to(p).as_posix() for f in stage]
assert all('/private/' not in x and not x.endswith('MANIFEST.json') and '/controls/' not in x for x in relative)
write(o / 'integration-guard.json', {'baseline_head': head, 'changed_task_indices': [671, 672],
    'all_other_tasks_preserved': True, 'contribution_task673_unchanged_unqueried': True,
    'other_top_level_preserved_except_progress_snapshot': True, 'journal_prefix_preserved': True,
    'frozen_sha256': v['frozen_sha256'], 'proof_sha256': v['proof_sha256'],
    'author_root104files_and_modes_unchanged': True, 'review_root71files_and_modes_unchanged': True,
    'immutable_author_input_records': 21, 'artifact_checks': '67 files/20 directories/three anchors matched; no mathematical gate',
    'adopted_correctness': gate, 'contribution_gate': None, 'accepted': False, 'count_change': 0,
    'new_task_dispatched': False, 'no_downstream_work': True,
    'count': 19, 'remaining': 1, 'latestAcceptance': 'R041', 'publication': 'STOPPED',
    'stage_allowlist': relative, 'protected_excluded': baseline['protected']})
assert snapshot(a) == load(o / 'private/author-root-before.json')
assert snapshot(r) == load(o / 'private/review-root-before.json')
assert head == git('rev-parse', 'HEAD').decode().strip()
subprocess.run(['git', 'add', '--', *relative], check=True)
assert set(git('diff', '--cached', '--name-only').decode().splitlines()) == {'openai-proof-research/' + x for x in relative}
for rel in relative:
    assert git('show', ':openai-proof-research/' + rel) == (p / rel).read_bytes()
print(json.dumps({'status': 'CORRECTNESS_PASS_INTEGRATED_AND_STAGED', 'head': head,
    'files': len(relative), 'correctness': 'PASS_FULL_SCOPE', 'contribution': None,
    'count': 19, 'remaining': 1, 'new_task_dispatched': False}, indent=2))
