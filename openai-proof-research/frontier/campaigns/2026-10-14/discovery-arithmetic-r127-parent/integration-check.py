#!/usr/bin/env python3
"""Arithmetic127 archive guard; preserve nominee/review state and full scopes."""
import datetime,importlib.util,json,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2]
spec=importlib.util.spec_from_file_location('replay',O/'replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def main(mode):
 base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
 if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
 path=str((B/'tasks.json').relative_to(P));old=json.loads(git('show',head+':'+prefix+path));new=read(B/'tasks.json');assert len(old['tasks'])==len(new['tasks'])==545 and [i for i in range(545) if old['tasks'][i]!=new['tasks'][i]]==[541]
 assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
 s0,s=old['current_work_snapshot'],new['current_work_snapshot'];assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','arithmetic127_terminal_pending_intake'} and set(s)-set(s0)=={'arithmetic_r127_archive','arithmetic128_deferred_for_review_capacity'} and not set(s0)-set(s)
 t=new['tasks'][541];r=read(O/'task-status.json')['structuredContent'];assert all(t[k]==v for k,v in r.items()) and t['parent_disposition']=='PREFREEZE_NO_NOMINEE' and t['correctness']==t['contribution']=='UNREVIEWED' and not t['scope_frozen'] and t['nominee'] is None and not t['accepted'] and t['count_change']==0
 assert s['t3_dispatch_observations']==s0['t3_dispatch_observations'] and s['t3_last_polled_running']==[] and s['t3_current_confirmed_running']==[new['tasks'][j]['taskId'] for j in [542,543,544]] and s['fresh_discovery_current']==[new['tasks'][542]['output']]
 assert not s['arithmetic127_terminal_pending_intake']['parent_archive_pending'] and s['arithmetic127_terminal_pending_intake']['resolved_parent_intake']=='discovery-arithmetic-r127-parent/intake.json'
 defer=read(O/'arithmetic128-deferral.json');assert defer['active_task_indices']==[542,543,544] and not defer['arithmetic128_brief_created'] and not defer['arithmetic128_root_created'] and not defer['arithmetic128_dispatched'] and not defer['campaign_paused'] and not defer['accepted'] and defer['count_change']==0
 assert not (B/'fresh-arithmetic-discovery-r128').exists() and not (B/'expanded-target-2026-10-17/fresh-arithmetic-r128-brief.txt').exists()
 assert h.snap(B/'fresh-arithmetic-discovery-r127')==read(O/'observed-root.json')['root'] and all(h.sha(P/e['path'])==e['sha256'] for e in read(O/'replay.json')['stable_named_originals']) and h.sha(O/'assessment.md')==read(O/'intake.json')['assessment_sha256'] and read(O/'finite-diagnostic.json')['cases']==30
 assert h.snap(B/'fresh-structural-discovery-r161')==read(B/'discovery-structural-r161-parent/observed-root.json')['root'] and h.sha(B/'fresh-structural-discovery-r161/scope-frozen.md')=='b5c7b51d352e250df511fae5d3456ccbaa2756180111020b3108415c12a7d813' and h.sha(B/'fresh-structural-discovery-r161/author-proof.md')=='f522cf05688e557aa7934946ee79564ee55238f0057423135a58c4d9abee451a'
 for j in [542,543,544]:assert h.sha(B/new['tasks'][j]['brief'])==old['tasks'][j]['brief_sha256']
 assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
 files=read(O/'staging-allowlist.json')['files'];assert len(files)==len(set(files))==28 and not any('/private/' in p for p in files) and len([p for p in files if '/fresh-arithmetic-discovery-r127/' in p])==12 and not any('/fresh-structural-discovery-r161/' in p or '/structural-r161-proof-r1/' in p or '/structural-r161-contribution-r1/' in p or '/fresh-analytic-discovery-r156/' in p for p in files)
 expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
 if mode=='prestage':
  assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+path,prefix+'frontier/NEW-TEN-2026-10-14.md'}
  (O/'integration-validation.json').write_text(json.dumps(dict(observed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),baseline_head=head,changed_existing_task_indices=[541],new_tasks=0,other_tasks_and_snapshot_fields_unchanged=True,nominee_frozen_scope_and_proof_unchanged=True,independent_review_briefs_dispatches_and_gates_unchanged=True,arithmetic128_deferred_for_capacity_not_campaign_pause=True,sealed_root_stable_originals_journal_prefix_protected_files_unchanged=True,explicit_allowed_paths=28,newAccepted=19,remaining=1,publication='STOPPED',mathematical_gate_assigned=False),indent=2)+'\n')
 else:
  if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
  else:
   assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
  assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes() for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
 print(json.dumps(dict(phase=mode,files=28,tasks=545,count=19,remaining=1,nominee_and_review_state_unchanged=True)))
if __name__=='__main__':main(sys.argv[1])
