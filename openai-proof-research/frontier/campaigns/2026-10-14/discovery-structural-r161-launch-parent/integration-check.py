#!/usr/bin/env python3
"""Guard the prospective Structural161 launch; no mathematical gate."""
import datetime,hashlib,importlib.util,json,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2]
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def main(mode):
 base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
 if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
 path=str((B/'tasks.json').relative_to(P));old=json.loads(git('show',head+':'+prefix+path));new=read(B/'tasks.json');assert len(old['tasks'])==540 and len(new['tasks'])==541 and old['tasks']==new['tasks'][:540]
 assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
 s0,s=old['current_work_snapshot'],new['current_work_snapshot'];assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','fresh_discovery_current','t3_current_confirmed_running','t3_dispatch_observations','structural161_deferred_for_initial_exclusions'} and set(s)-set(s0)=={'structural161_prospective_isolation','structural161_source_selection_preparation'} and not set(s0)-set(s)
 assert s['t3_dispatch_observations'][:-1]==s0['t3_dispatch_observations'] and s['t3_last_polled_running']==[]
 t=new['tasks'][540];raw=read(O/'r161-dispatch.json')['structuredContent'];assert all(t[k]==v for k,v in raw.items()) and raw['status']=='running' and raw['workState']=='working' and not raw['hasPendingChildRuns'] and not raw['hasPendingQuestion'];assert t['providerInstanceId']=='codex' and t['model']=='gpt-6-astra' and {e['id']:e['value'] for e in t['options']}=={'reasoningEffort':'high','serviceTier':'default'} and not t['accepted'] and t['count_change']==0
 assert s['fresh_discovery_current']==[new['tasks'][j]['output'] for j in [538,539,540]] and s['t3_current_confirmed_running']==[new['tasks'][j]['taskId'] for j in [538,539,540]]
 receipt=read(O/'prospective-isolation.json');assert receipt['before_structural161_brief_or_root'] and receipt['no_active_peer_status_poll_body_read_or_steer'] and len(receipt['both_original_initial_peer_briefs'])==2
 for e,i in zip(receipt['both_original_initial_peer_briefs'],[538,539]):
  peer=old['tasks'][i];assert e['task_index']==i and e['taskId']==peer['taskId'] and e['brief']==peer['brief'] and sha(B/e['brief'])==e['sha256']==peer['brief_sha256'];assert all(x in (B/e['brief']).read_text() for x in ['*structural*r161*','*structural*r162*'])
 text=(B/t['brief']).read_text();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';assert sha(B/t['brief'])==t['brief_sha256'];assert text.split(marker)[1]==(B/'expanded-target-2026-10-17/fresh-structural-r160-brief.txt').read_text().split(marker)[1];assert all(x in text for x in ['*arithmetic*r126*','*analytic*r155*','*arithmetic*r127*','*analytic*r156*','*t360s147*','Source126','Exponential-PSD-rank-of-positively-shifted-matching-matrices-October-5-2026'])
 private=read(O/'source-selection-private.json');assert private['source_number']=='126' and private['actual_source_body_not_yet_read'] and private['parent_catalogue_blocks_displayed']==['126'] and private['no_additional_family_screen_authorized'] and len(private['canonical_objects'])==12;assert all(e['path'].startswith(private['confirmed_prefix']) for e in private['canonical_objects']);assert private['erroneous_initial_path_metadata_count']==17
 f=s['structural161_deferred_for_initial_exclusions'];assert f['resolved_by_structural161_dispatch'] and not f['no_new_structural_brief_root_or_task'] and f['structural161_taskId']==t['taskId'] and not f['waiting_for_analytic155_initial_exclusion'] and not f['campaign_paused']
 assert all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
 # Completed Analytic154 seal and its selected originals must remain untouched.
 spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
 assert h.snap(B/'fresh-analytic-discovery-r154')==read(B/'discovery-analytic-r154-parent/observed-root.json')['root'] and all(sha(P/e['path'])==e['sha256'] for e in read(B/'discovery-analytic-r154-parent/replay.json')['stable_named_originals'])
 files=read(O/'staging-allowlist.json')['files'];assert len(files)==len(set(files))==10 and not any('/fresh-structural-discovery-r161/' in p or '/private/' in p or 'source-selection-private' in p for p in files);expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
 if mode=='prestage':
  assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+path,prefix+'frontier/NEW-TEN-2026-10-14.md'}
  (O/'integration-validation.json').write_text(json.dumps(dict(observed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),baseline_head=head,existing_tasks_unchanged=540,new_task_index=540,prospective_both_initial_peer_guards_authenticated=True,confirmed_pinned_source_paths_only=True,source_body_not_read_by_parent=True,metadata_query_error_disclosed=True,private_selection_not_staged=True,complete_standing_brief_preserved=True,completed_root_and_stable_originals_unchanged=True,journal_prefix_and_protected_files_unchanged=True,explicit_paths=10,newAccepted=19,remaining=1,publication='STOPPED',mathematical_gate_assigned=False),indent=2)+'\n')
 else:
  if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
  else:
   assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
  assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes() for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
 print(json.dumps(dict(phase=mode,files=10,tasks=541,count=19,remaining=1,initial_prompt_guards_and_archive_preserved=True)))
if __name__=='__main__':main(sys.argv[1])
