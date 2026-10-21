#!/usr/bin/env python3
"""Three fresh mutually isolated actual dispatches after immutable full-scope closure."""
import datetime,importlib.util,json,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;A=O.parent;B=A.parent;P=B.parents[2]
sp=importlib.util.spec_from_file_location('helpers',A/'replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def main(mode):
 base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
 if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
 path=str((B/'tasks.json').relative_to(P));old=json.loads(git('show',head+':'+prefix+path));new=read(B/'tasks.json');assert len(old['tasks'])==564 and len(new['tasks'])==567 and old['tasks']==new['tasks'][:564]
 assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
 s0,s=old['current_work_snapshot'],new['current_work_snapshot'];assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','t3_current_confirmed_running','fresh_discovery_current','t3_dispatch_observations'} and set(s)-set(s0)=={'distinct_discovery_after_analytic161'} and not set(s0)-set(s)
 assert s['t3_dispatch_observations'][:-3]==s0['t3_dispatch_observations'] and not s['t3_last_polled_running'] and not s['pending_terminal_intakes_20261021'] and s['fresh_discovery_current']==[new['tasks'][i]['output'] for i in [564,565,566]] and s['t3_current_confirmed_running']==[new['tasks'][i]['taskId'] for i in [564,565,566]]
 receipt=read(O/'prospective-isolation.json');assert receipt['all_reviews_terminal_before_new_dispatch'] and receipt['before_all_fresh_roots_and_dispatches'] and receipt['all_three_original_initial_briefs_reciprocally_exclude_current_and_future_rounds'] and receipt['all_original_standing_suffixes_preserved_bytes']==5570 and receipt['no_peer_body_status_activity_read_or_steer'] and len(receipt['briefs'])==3
 marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=(B/'expanded-target-2026-10-17/fresh-arithmetic-r133-brief.txt').read_text().split(marker)[1];assert len(standing.encode())==5570
 for i,e in zip([564,565,566],receipt['briefs']):
  raw=read(O/(e['role']+'-r'+str(e['round'])+'-dispatch.json'))['structuredContent'];t=new['tasks'][i];assert all(t[k]==v for k,v in raw.items()) and t['brief']==e['brief'] and t['output']==e['output'] and t['source_family_navigation']==e['family'] and h.sha(B/t['brief'])==t['brief_sha256']==e['brief_sha256'] and t['providerInstanceId']=='codex' and t['model']=='gpt-6-astra' and {x['id']:x['value'] for x in t['options']}=={'reasoningEffort':'high','serviceTier':'default'} and t['status']=='running' and not t['hasPendingChildRuns'] and not t['hasPendingQuestion'] and t['pendingApproval'] is None and not t['accepted'] and t['count_change']==0
  text=(B/t['brief']).read_text();assert text.split(marker)[1]==standing and all(p in text for p in ['*analytic*r162*','*structural*r168*','*arithmetic*r134*','*analytic*r163*','*structural*r169*','*arithmetic*r135*','*analytic*r164*','*structural*r170*','*arithmetic*r136*','*t337a161*','*t126s161*','*t360s147*'])
 nav=read(O/'private/source-selection.json');tree=read(P/'sources/preprints-tree.json');assert h.sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b' and len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
 for key,n in [('analytic162',6),('structural168',3),('arithmetic134',1)]:assert len(nav[key])==n and all(entries[e['main']['path']]==e['main'] for e in nav[key])
 n=read(O/'private/navigation-receipt.json');assert h.sha(P/'sources/CONTENTS.md')==n['catalogue_original_sha256'] and not n['whole_map_decoded_or_displayed'] and len(n['selected_family_blocks'])==6
 for e in n['selected_family_blocks']:
  q=O/'private/catalogue'/('%03d.md'%e['family']);assert h.sha(q)==e['selected_sha256'] and q.read_bytes()==(P/'sources/CONTENTS.md').read_bytes()[e['start_byte']:e['end_byte_exclusive']]
 closed=read(A/'contribution-r1-adoption/adoption.json');assert closed['verdict']=='TECHNICAL' and closed['correctness']=='PASS' and closed['count_change']==0 and closed['correctness_condition']=='DISCHARGED_BY_INDEPENDENT_ENTIRE_UNCHANGED_FROZEN_SCOPE_PASS' and h.sha(A/'contribution-r1-adoption/assessment.md')==closed['assessment_sha256']==receipt['full_analytic161_closed_assessment_fixed_sha256']
 for root,parent in [('fresh-analytic-discovery-r161',A),('analytic-r161-proof-r1',A/'proof-r1-adoption'),('analytic-r161-contribution-r1',A/'contribution-r1-adoption')]:assert h.snap(B/root)==read(parent/'observed-root.json')['root']
 assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
 files=read(O/'staging-allowlist.json')['files'];assert len(files)==len(set(files))==14 and not any('/private/' in p or any('/'+e['output']+'/' in p for e in receipt['briefs']) for p in files)
 expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
 if mode=='prestage':
  assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+path,prefix+'frontier/NEW-TEN-2026-10-14.md'}
  (O/'integration-validation.json').write_text(json.dumps({'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_head':head,'changed_existing_task_indices':[],'new_task_indices':[564,565,566],'other_tasks_and_snapshot_fields_unchanged':True,'three_actual_codex_astra_high_standard_dispatches':True,'complete_original_standing_suffixes_preserved':True,'original_initial_mutual_current_future_exclusions_precede_dispatch':True,'selected_canonical_entry_objects_confirmed':True,'protected_catalogue_and_source_navigation_local_unstaged':True,'closed_full_scope_PASS_TECHNICAL_disposition_and_three_sealed_roots_unchanged':True,'journal_prefix_and_protected_unrelated_files_unchanged':True,'explicit_allowed_paths':14,'newAccepted':19,'remaining':1,'publication':'STOPPED','mathematical_gate_assigned':False},indent=2)+'\n')
 else:
  if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
  else:
   assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
  assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes() for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
 print(json.dumps({'phase':mode,'files':14,'tasks':567,'new_discoveries':3,'count':19,'remaining':1,'closed_scope_and_sealed_roots_unchanged':True}))
if __name__=='__main__':main(sys.argv[1])
