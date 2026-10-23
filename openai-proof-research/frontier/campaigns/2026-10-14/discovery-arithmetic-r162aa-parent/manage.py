#!/usr/bin/env python3
"""One-time compare-and-swap intake and next-round registration; parent records only."""
from pathlib import Path
from datetime import datetime, timezone
import copy
import fnmatch
import hashlib
import json
import re
import subprocess

P = Path(__file__).resolve().parents[4]
B = P / 'frontier/campaigns/2026-10-14'
D = Path(__file__).resolve().parent
N = B / 'discovery-arithmetic-r162ab-parent'
TP = 'frontier/campaigns/2026-10-14/tasks.json'
JP = 'frontier/NEW-TEN-2026-10-14.md'
def git(*args):
    return subprocess.check_output(['git', *args], cwd=P)
def sha(data):
    return hashlib.sha256(data).hexdigest()
def dump(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')
assert not git('diff', '--cached', '--name-only').strip()
head = git('rev-parse', 'HEAD').decode().strip()
raw_t = git('show', head + ':openai-proof-research/' + TP)
raw_j = git('show', head + ':openai-proof-research/' + JP)
assert (P / TP).read_bytes() == raw_t and (P / JP).read_bytes() == raw_j
old = json.loads(raw_t)
new = copy.deepcopy(old)
assert old['newAccepted'] == 19 and old['target'] == 20
assert old['tasks'][709]['status'] == 'running'
assert all(t.get('clientRequestId') != 'twenty-20261023-fresh-arithmetic-r162ab-codex-astra-r1' for t in old['tasks'])
baseline = json.loads((D / 'intake-baseline.json').read_text())
for name, anchor in baseline['protected'].items():
    assert sha((P / name).read_bytes()) == anchor

# Recheck original-brief hashes and all three new namespace matches at integration.
guard = json.loads((N / 'prospective-isolation.json').read_text())
current_foreign = [(i,t) for i,t in enumerate(old['tasks']) if i != 709 and t.get('status') in {'running','queued','waiting'} and 'brief' in t]
guard_by_index = {x['task_index']: x for x in guard['original_foreign_brief_guard_checks']}
for i,t in current_foreign:
    original = (P / t['brief']).read_bytes()
    g = guard_by_index[i]
    assert t['brief'] == g['original_brief'] and sha(original) == g['sha256']
    patterns = [p for p in re.findall(r'\*[^\s,;()]*\*', original.decode()) if p not in {'*','**'}]
    assert all(any(fnmatch.fnmatchcase(n.casefold(),p.casefold()) for p in patterns) for n in guard['namespaces'])

now = datetime.now(timezone.utc).isoformat()
terminal = json.loads((D / 'task-status.json').read_text())['structuredContent']
dispatch = json.loads((N / 'dispatch.json').read_text())['structuredContent']
assert terminal['taskId'] == old['tasks'][709]['taskId']
assert terminal['status'] == 'completed' and terminal['workState'] == 'result_available'
assert not terminal['hasPendingChildRuns'] and not terminal['hasPendingQuestion'] and terminal['pendingApproval'] is None
assert dispatch['status'] in {'running','queued'} and dispatch['providerInstanceId'] == 'codex' and dispatch['model'] == 'gpt-6-astra'
assert {x['id']:x['value'] for x in dispatch['options']} == dict(reasoningEffort='high', serviceTier='default')
own = new['tasks'][709]
own.update(terminal)
own.update(observed_utc=now, disposition='ARCHIVED_PREFREEZE_NO_NOMINEE', parent_intake='discovery-arithmetic-r162aa-parent/intake.json', parent_assessment='discovery-arithmetic-r162aa-parent/assessment.md', artifact_verification='discovery-arithmetic-r162aa-parent/verification.json', frozen_statement=False, correctness_gate=None, contribution_gate=None, accepted=False, count_change=0, full_scope_preserved=True, mathematical_gap='ONE rational symmetric <=2n^2-facet body in EVERY sufficiently large dimension with same-volume c*n*log(n) obstruction against EVERY locally finite translative covering; equivalent all-window/all-center-list inequality remains unproved.', status_provenance='Own task_status terminal intake only; no watcher or foreign live query.')
prep = json.loads((N / 'brief-preparation.json').read_text())
brief = P / prep['brief']
assert sha(brief.read_bytes()) == prep['sha256'] and len(brief.read_bytes()) == prep['bytes']
record = copy.deepcopy(dispatch)
record.update(observed_utc=now, role='research', round=1, target=dict(providerInstanceId='codex',model='gpt-6-astra',options=dict(reasoningEffort='high',serviceTier='default')), title='Arithmetic162ab: confirmed subgaussian log-Sobolev operative-proof discovery', clientRequestId='twenty-20261023-fresh-arithmetic-r162ab-codex-astra-r1', parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177', output='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ab/', brief=prep['brief'], brief_sha256=prep['sha256'], brief_bytes=prep['bytes'], submitted_prompt_contains_full_brief=True, source_index=93, source_family_navigation='DISTINCT Source093; selected catalogue[155355,156394),one confirmed folder,13 blobs/17 complete-tree entries including roots,actual build/main.tex. Source094 body not decoded. Parent metadata only.', round_namespace='Distinct subgaussian log-Sobolev family. Full quadratic-facet covering diagnostic and every previous scope preserved. Entire stipulated dimension-free subgaussian log-concave LSI and stronger operative source operations are paid where proved.', all_previous_literal_guards_and5570_standing_bytes_retained=True, dispatch_receipt='discovery-arithmetic-r162ab-parent/dispatch.json', prospective_isolation='discovery-arithmetic-r162ab-parent/prospective-isolation.json', accepted=False, count_change=0, parent_count_at_dispatch=19, publication='STOPPED', status_provenance='Actual async delegate_task dispatch, explicit high/default options verified; no polling or watcher.')
index = len(new['tasks'])
new['tasks'].append(record)
note = 'Arithmetic162aa archived PREFREEZE/no nominee; full quadratic-facet covering-density diagnostic remains unproved. Distinct Arithmetic162ab dispatched on Source093 subgaussian log-concave logarithmic Sobolev inequalities, Codex/GPT-6 Astra/high/default. Campaign19/20 latestR041 one remains; publicationSTOPPED. All foreign task records preserved.'
new['last_parent_progress'] = note
snap = new['current_work_snapshot']
snap.update(observed_utc=now, note=note)
snap['arithmetic_r162aa_archive'] = dict(task_index=709, status='PREFREEZE_NO_NOMINEE', intake='discovery-arithmetic-r162aa-parent/intake.json', full_diagnostic='Numerical c>0,n0; EVERY n>=n0 has ONE bounded full-dimensional rational origin-symmetric polytope with <=2n^2 facets and unrestricted translative covering density >=c*n*log(n),using actual same body volume and EVERY locally finite center arrangement.', unpaid_operation=own['mathematical_gap'], correctness_gate=None, contribution_gate=None, accepted=False, count_change=0)
snap['arithmetic_r162ab_dispatch'] = dict(task_index=index,taskId=dispatch['taskId'],status=dispatch['status'],brief=prep['brief'],source='093',catalogue_extent=[155355,156394],original_brief_guards_checked_before_creation=True,private_local_inputs_and_metadata_retained=True,foreign_live_queries=False,publication='STOPPED')
changed = [i for i,(a,b) in enumerate(zip(old['tasks'],new['tasks'])) if a != b]
assert changed == [709]
assert all(old[k] == new[k] for k in old if k not in {'tasks','last_parent_progress','current_work_snapshot'})
assert all(snap[k] == v for k,v in old['current_work_snapshot'].items() if k not in {'observed_utc','note','arithmetic_r162aa_archive','arithmetic_r162ab_dispatch'})
addition = ('\n\n### Arithmetic162aa intake and distinct Arithmetic162ab dispatch — '+now+'\n\n'+note+'\n\nParent assessment: [discovery-arithmetic-r162aa-parent/assessment.md](campaigns/2026-10-14/discovery-arithmetic-r162aa-parent/assessment.md). Read-only artifact checks matched 65 selected files,27 canonical bindings and the unchanged 68-file root; these are not mathematical gates. No theorem was frozen. The complete same-body/all-center diagnostic and stronger paid reductions remain in the local packet. Actual primary/transitive and isolation limits are recorded. New full original brief: `campaigns/2026-10-14/expanded-target-2026-10-17/fresh-arithmetic-r162ab-brief.txt`; all previous literal guards and5570 standing bytes retained. Original-brief checks preceded namespace creation. Asynchronous research only; no polling,watcher,public action or count change.\n').encode()
next_t = (json.dumps(new,ensure_ascii=False,indent=2)+'\n').encode()
next_j = raw_j + addition
dump(D / 'coordination-rebase.json',dict(intake_head=baseline['head'],integration_head=head,head_advanced=head!=baseline['head'],before_task_count=len(old['tasks']),after_task_count=len(new['tasks']),changed_old_task_indices=changed,all_other_tasks_preserved=True,all_other_top_fields_preserved=True,journal_prefix_preserved=True,protected_modifications_preserved=True,tasks_before_sha256=sha(raw_t),tasks_after_sha256=sha(next_t),journal_before_sha256=sha(raw_j),journal_after_sha256=sha(next_j),no_foreign_live_queries=True))
dump(N / 'registration.json',dict(task_index=index,taskId=dispatch['taskId'],status_at_dispatch=dispatch['status'],provider_model_options_verified=True,count_change=0,publication='STOPPED'))
assert git('rev-parse','HEAD').decode().strip() == head
assert (P / TP).read_bytes() == raw_t and (P / JP).read_bytes() == raw_j
(P / TP).write_bytes(next_t)
(P / JP).write_bytes(next_j)
print(json.dumps(dict(own_archived=709,new_task_index=index,changed_old_task_indices=changed,task_count=len(new['tasks']),campaign_count=19,head=head)))
