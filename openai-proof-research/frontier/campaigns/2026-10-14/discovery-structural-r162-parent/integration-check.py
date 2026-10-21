#!/usr/bin/env python3
"""Guard one source-selection-failure archive; preserve all grades and counts."""
import datetime,importlib.util,json,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2]
sp=importlib.util.spec_from_file_location('replay',O/'replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def main(mode):
 base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
 if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
 old=json.loads(git('show',head+':'+prefix+str((B/'tasks.json').relative_to(P))));new=read(B/'tasks.json');assert len(old['tasks'])==len(new['tasks'])==548 and [i for i in range(548) if old['tasks'][i]!=new['tasks'][i]]==[546]
 assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
 s0,s=old['current_work_snapshot'],new['current_work_snapshot'];assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','structural162_terminal_pending_intake'} and set(s)-set(s0)=={'structural_r162_archive','structural163_deferred'} and not set(s0)-set(s)
 t=new['tasks'][546];raw=read(O/'task-status.json')['structuredContent'];assert all(t[k]==v for k,v in raw.items());assert t['parent_disposition']=='PREFREEZE_NO_NOMINEE' and t['failure_kind']=='NO_MATCHING_PINNED_MANUSCRIPT_SELECTED' and not t['discovery_requirements_met'] and not t['source_reading_requirement_met'] and not t['sustained_mathematical_derivation'];assert t['correctness']==t['contribution']=='UNREVIEWED' and not t['scope_frozen'] and t['nominee'] is None and not t['accepted'] and t['count_change']==0
 assert h.snap(B/'fresh-structural-discovery-r162')==read(O/'observed-root.json')['root'] and all(h.sha(P/e['path'])==e['sha256'] for e in read(O/'replay.json')['stable_named_originals']) and h.sha(O/'assessment.md')==read(O/'intake.json')['assessment_sha256']
 receipt=read(O/'structural163-deferral.json');assert not receipt['structural163_brief_or_root_created'] and not receipt['arithmetic128_initial_has_structural163_guard'] and receipt['analytic157_initial_has_structural163_guard']
 for k,i in [('arithmetic128',545),('analytic157',547)]:assert h.sha(B/new['tasks'][i]['brief'])==receipt[k+'_initial_sha256']==new['tasks'][i]['brief_sha256']
 assert not (B/'fresh-structural-discovery-r163').exists() and not (B/'expanded-target-2026-10-17/fresh-structural-r163-brief.txt').exists()
 assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
 files=read(O/'staging-allowlist.json')['files'];assert len(files)==len(set(files))==22 and not any('/private/' in p for p in files) and len([p for p in files if '/fresh-structural-discovery-r162/' in p])==8
 expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']};shared={prefix+str((B/'tasks.json').relative_to(P)),prefix+'frontier/NEW-TEN-2026-10-14.md'}
 if mode=='prestage':
  assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|shared
  (O/'integration-validation.json').write_text(json.dumps(dict(observed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),baseline_head=head,changed_existing_task_indices=[546],no_dispatch=True,other_tasks_and_snapshot_fields_unchanged=True,sealed_root_and_stable_originals_unchanged=True,discovery_requirements_met=False,mathematical_gate_assigned=False,explicit_allowed_paths=22,newAccepted=19,remaining=1,publication='STOPPED'),indent=2)+'\n')
 else:
  if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
  else:
   assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
  assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes() for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
 print(json.dumps(dict(phase=mode,files=22,tasks=548,count=19,remaining=1,mathematical_gate=False)))
if __name__=='__main__':main(sys.argv[1])
