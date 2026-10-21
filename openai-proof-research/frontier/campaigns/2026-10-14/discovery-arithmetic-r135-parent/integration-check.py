#!/usr/bin/env python3
"""Bounded integration checks for the Arithmetic135 archive and Arithmetic136 dispatch."""
import datetime,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2]
sp=importlib.util.spec_from_file_location('replay',O/'replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def main(mode):
 base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
 if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
 path=str((B/'tasks.json').relative_to(P));old=json.loads(git('show',head+':'+prefix+path));new=read(B/'tasks.json');assert len(old['tasks'])==571 and len(new['tasks'])==572 and [i for i in range(571)if old['tasks'][i]!=new['tasks'][i]]==[568]
 assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
 s0,s=old['current_work_snapshot'],new['current_work_snapshot'];assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','t3_current_confirmed_running','fresh_discovery_current','t3_dispatch_observations'} and set(s)-set(s0)=={'arithmetic_r135_archive','arithmetic136_prospective_isolation'} and not set(s0)-set(s)
 assert s['t3_dispatch_observations'][:-1]==s0['t3_dispatch_observations'] and not s['t3_last_polled_running'] and s['fresh_discovery_current']==[new['tasks'][i]['output']for i in [569,570,571]] and s['t3_current_confirmed_running']==[new['tasks'][i]['taskId']for i in [569,570,571]]
 assert not s['pending_terminal_intakes_20261021']
 for i,n in [(568,'task-status.json'),(571,'arithmetic-r136-dispatch.json')]:
  raw=read(O/n)['structuredContent'];assert all(new['tasks'][i][k]==v for k,v in raw.items())
 t=new['tasks'][568];assert t['parent_disposition']=='PREFREEZE_NO_NOMINEE' and not t['scope_frozen'] and t['nominee'] is None and t['correctness']==t['contribution']=='UNREVIEWED' and not t['accepted'] and t['count_change']==0
 t=new['tasks'][571];assert t['providerInstanceId']=='codex' and t['model']=='gpt-6-astra' and {e['id']:e['value']for e in t['options']}=={'reasoningEffort':'high','serviceTier':'default'} and t['status']=='running' and not t['hasPendingChildRuns'] and not t['hasPendingQuestion'] and t['pendingApproval'] is None and not t['accepted'] and t['count_change']==0 and t['source_family_navigation']==54
 receipt=read(O/'prospective-isolation.json');assert receipt['before_arithmetic136_brief_or_root'] and receipt['both_original_initial_active_peer_briefs_exclude136'] and receipt['no_active_peer_body_read_poll_or_steer']
 for e,i in zip(receipt['existing_active_peer_original_initial_briefs'],[569,570]):
  peer=old['tasks'][i];assert e['task_index']==i and e['taskId']==peer['taskId'] and e['brief']==peer['brief'] and h.sha(B/e['brief'])==e['sha256']==peer['brief_sha256'] and e['literal_existing_exclusion'] in (B/e['brief']).read_text()
 marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';text=(B/t['brief']).read_text();assert h.sha(B/t['brief'])==t['brief_sha256']==read(O/'intake.json')['brief_sha256'] and text.split(marker)[1]==(B/'expanded-target-2026-10-17/fresh-arithmetic-r135-brief.txt').read_text().split(marker)[1] and len(text.split(marker)[1].encode())==5570 and all(p in text for p in ['*arithmetic*r136*','*analytic*r163*','*structural*r170*','*analytic*r164*','*structural*r171*','*arithmetic*r137*','*t337a161*'])
 nav=read(O/'private/source054-navigation.json');tree=read(P/'sources/preprints-tree.json');assert h.sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b' and len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};assert entries[nav['main']['path']]==nav['main'] and nav['main']['path'] in text and nav['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
 n=read(O/'private/catalogue-navigation.json');assert [e['family']for e in n['selected']]==[54] and not n['whole_map_decoded'] and h.sha(P/'sources/CONTENTS.md')==n['catalogue_sha256']
 for e in n['selected']:assert h.sha(O/'private'/('catalogue-%03d.md'%e['family']))==e['selected_sha256']
 observed=read(O/'observed-root.json');root=B/'fresh-arithmetic-discovery-r135';assert h.snap(root)==observed['root'] and stat.S_IMODE(root.stat().st_mode)==observed['root_mode'] and all(h.sha(P/e['path'])==e['sha256']for e in read(O/'replay.json')['stable_named_originals']) and h.sha(O/'assessment.md')==read(O/'intake.json')['assessment_sha256']
 A=B/'discovery-analytic-r161-parent'
 for r,p in [('fresh-analytic-discovery-r161',A),('analytic-r161-proof-r1',A/'proof-r1-adoption'),('analytic-r161-contribution-r1',A/'contribution-r1-adoption')]:assert h.snap(B/r)==read(p/'observed-root.json')['root']
 assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
 files=read(O/'staging-allowlist.json')['files'];assert len(files)==len(set(files))==23 and len([p for p in files if '/fresh-arithmetic-discovery-r135/' in p])==9 and not any('/private/' in p or '/controls/' in p or '/fresh-analytic-discovery-r163/' in p or '/fresh-structural-discovery-r170/' in p or '/fresh-arithmetic-discovery-r136/' in p or p.endswith(('/observed-root.json','/replay.json'))for p in files)
 expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
 if mode=='prestage':
  assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+path,prefix+'frontier/NEW-TEN-2026-10-14.md'}
  (O/'integration-validation.json').write_text(json.dumps({'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_head':head,'changed_existing_task_indices':[568],'new_task_indices':[571],'pending_terminal_intakes':[],'other_tasks_and_snapshot_fields_unchanged':True,'original_initial_peer_exclusions_precede_new_brief_root_dispatch':True,'complete_original_standing_suffix_preserved':True,'selected_canonical_entry_confirmed_metadata_only':True,'sealed_archive_and_analytic161_author_review_roots_unchanged':True,'protected_identity_replay_navigation_local_unstaged':True,'journal_prefix_and_protected_unrelated_files_unchanged':True,'explicit_allowed_paths':23,'newAccepted':19,'remaining':1,'publication':'STOPPED','mathematical_gate_assigned':False},indent=2)+'\n')
 else:
  if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
  else:
   assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
  assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes()for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
 print(json.dumps({'phase':mode,'files':23,'tasks':572,'count':19,'remaining':1,'sealed_roots_unchanged':True}))
if __name__=='__main__':main(sys.argv[1])
