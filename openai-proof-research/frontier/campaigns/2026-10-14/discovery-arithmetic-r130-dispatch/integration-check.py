#!/usr/bin/env python3
"""Check source-confirmed Arithmetic130 initial dispatch, preserving all prior work."""
import datetime,hashlib,json,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2]
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def main(mode):
 base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
 if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
 path=str((B/'tasks.json').relative_to(P));old=json.loads(git('show',head+':'+prefix+path));new=read(B/'tasks.json');assert len(old['tasks'])==551 and len(new['tasks'])==552 and old['tasks']==new['tasks'][:551]
 assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
 s0,s=old['current_work_snapshot'],new['current_work_snapshot'];assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','fresh_discovery_current','t3_current_confirmed_running','t3_dispatch_observations','arithmetic130_deferred'} and set(s)-set(s0)=={'arithmetic130_dispatch'} and not set(s0)-set(s)
 assert s['t3_dispatch_observations'][:-1]==s0['t3_dispatch_observations'] and s['t3_last_polled_running']==[]
 t=new['tasks'][551];raw=read(O/'dispatch.json')['structuredContent'];assert all(t[k]==v for k,v in raw.items()) and t['providerInstanceId']=='codex' and t['model']=='gpt-6-astra' and {e['id']:e['value'] for e in t['options']}=={'reasoningEffort':'high','serviceTier':'default'} and t['status']=='running' and not t['hasPendingChildRuns'] and not t['hasPendingQuestion'] and not t['accepted'] and t['count_change']==0
 assert s['fresh_discovery_current']==[new['tasks'][i]['output'] for i in [549,550,551]] and s['t3_current_confirmed_running']==[new['tasks'][i]['taskId'] for i in [549,550,551]]
 receipt=read(O/'prospective-isolation.json');assert receipt['before_arithmetic130_brief_or_root'] and receipt['both_existing_original_initial_briefs_exclude_future130'] and receipt['no_active_peer_body_read_poll_or_steer'] and len(receipt['existing_active_peer_original_initial_briefs'])==2
 for e,i in zip(receipt['existing_active_peer_original_initial_briefs'],[549,550]):
  peer=old['tasks'][i];assert e['task_index']==i and e['taskId']==peer['taskId'] and e['brief']==peer['brief'] and sha(B/e['brief'])==e['sha256']==peer['brief_sha256'] and '*arithmetic*r130*' in (B/e['brief']).read_text()
 text=(B/t['brief']).read_text();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';assert sha(B/t['brief'])==t['brief_sha256'] and text.split(marker)[1]==(B/old['tasks'][548]['brief']).read_text().split(marker)[1] and len(text.split(marker)[1].encode())==5570
 assert all(x in text for x in ['*analytic*r158*','*structural*r163*','*analytic*r159*','*structural*r164*','*t126s161*','TECHNICAL','Source017','The-irrationality-exponent-of-pi-is-2-September-24-2026/build/main.tex','sections/determinant.tex,interpolation.tex,series.tex,conclusion.tex'])
 assert sha(B/'discovery-analytic-r157-parent/assessment.md')==read(B/'discovery-analytic-r157-parent/intake.json')['assessment_sha256']

 assert all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
 files=read(O/'staging-allowlist.json')['files'];assert len(files)==len(set(files))==11 and not any('/private/' in p or '/fresh-arithmetic-discovery-r130/' in p for p in files)
 expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
 if mode=='prestage':
  assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+path,prefix+'frontier/NEW-TEN-2026-10-14.md'}
  (O/'integration-validation.json').write_text(json.dumps(dict(observed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),baseline_head=head,existing_tasks_unchanged=True,new_task_index=551,both_original_initial_peer_exclusions=True,complete_original_standing_brief_preserved=True,source_confirmed_from_canonical_tree_metadata=True,source_reading_not_claimed_by_parent=True,protected_originals_unchanged=True,explicit_allowed_paths=11,newAccepted=19,remaining=1,publication='STOPPED',mathematical_gate_assigned=False),indent=2)+'\n')
 else:
  if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
  else:
   assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
  assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes() for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
 print(json.dumps(dict(phase=mode,files=11,tasks=552,count=19,remaining=1,mathematical_gate=False)))
if __name__=='__main__':main(sys.argv[1])
