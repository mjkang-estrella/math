#!/usr/bin/env python3
"""Narrow Structural174 archive and actual confirmed Arithmetic137 dispatch."""
import datetime,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2]
sp=importlib.util.spec_from_file_location('replay',O/'replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def git(*args):return subprocess.check_output(['git',*args],cwd=P)
def main(mode):
    base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
    if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
    rel=(B/'tasks.json').relative_to(P).as_posix();old=json.loads(git('show',head+':'+prefix+rel));new=read(B/'tasks.json');assert len(old['tasks'])==584 and len(new['tasks'])==585 and [i for i in range(584)if old['tasks'][i]!=new['tasks'][i]]==[581]
    assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
    s0=old['current_work_snapshot'];s=new['current_work_snapshot'];assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','t3_current_confirmed_running','fresh_discovery_current','t3_dispatch_observations','arithmetic137_preparation_deferred'} and set(s)-set(s0)=={'structural_r174_archive','arithmetic137_prospective_isolation'} and not set(s0)-set(s)
    assert s['t3_dispatch_observations'][:-1]==s0['t3_dispatch_observations'] and not s['pending_terminal_intakes_20261021'] and not s['t3_last_polled_running'] and s['fresh_discovery_current']==['fresh-arithmetic-discovery-r137'] and s['t3_current_confirmed_running']==[new['tasks'][i]['taskId']for i in [582,583,584]]
    for i,n in [(581,'task-status.json'),(584,'arithmetic-r137-dispatch.json')]:assert all(new['tasks'][i][k]==v for k,v in read(O/n)['structuredContent'].items())
    t=new['tasks'][581];assert t['parent_disposition']=='PREFREEZE_NO_NOMINEE' and not t['scope_frozen'] and t['nominee'] is None and t['correctness']==t['contribution']=='UNREVIEWED' and not t['accepted'] and t['count_change']==0
    intake=read(O/'intake.json');assert s['structural_r174_archive']==intake and h.sha(O/'assessment.md')==intake['assessment_sha256']
    t=new['tasks'][584];assert t['providerInstanceId']=='codex' and t['model']=='gpt-6-astra' and {x['id']:x['value']for x in t['options']}=={'reasoningEffort':'high','serviceTier':'default'} and t['status']=='running' and not t['hasPendingChildRuns'] and not t['hasPendingQuestion'] and t['pendingApproval'] is None and not t['accepted'] and t['count_change']==0 and t['source_family_navigation']==43
    pro=read(O/'prospective-isolation.json');assert pro['before_arithmetic137_root_and_brief'] and pro['both_original_initial_guards_cover_entire_arithmetic137_namespace'] and pro['no_live_peer_body_status_activity_read_poll_or_steer']
    for e in pro['existing_active_peer_original_initial_briefs']:
        peer=old['tasks'][e['task_index']];assert e['taskId']==peer['taskId'] and h.sha(B/e['brief'])==e['sha256']==peer['brief_sha256'] and e['literal_existing_exclusion'].encode()in(B/e['brief']).read_bytes()
    marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';text=(B/t['brief']).read_text();suffix=text.split(marker)[1];assert len(suffix.encode())==5570 and suffix==(B/'expanded-target-2026-10-17/fresh-analytic-r166-brief.txt').read_text().split(marker)[1] and h.sha(B/t['brief'])==t['brief_sha256']==pro['new_brief']['sha256']==intake['new_brief_sha256']
    nav=read(O/'private/source043-navigation.json');tree=read(P/'sources/preprints-tree.json');entries={e['path']:e for e in tree['tree']};assert len(tree['tree'])==13223 and not tree['truncated'] and h.sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b' and len(nav['entries'])==1 and all(entries[e['path']]==e for e in nav['entries']) and nav['entries'][0]['path']in text
    original_nav=B/'discovery-arithmetic-r136-parent/repair-r1-adoption/private'
    for n in ['source043-navigation.json','title-navigation.json','catalogue-043.md']:assert (O/'private'/n).read_bytes()==(original_nav/n).read_bytes()
    obs=read(O/'observed-root.json');root=B/'fresh-structural-discovery-r174';assert h.snap(root)==obs['root'] and stat.S_IMODE(root.stat().st_mode)==obs['root_mode'] and all(h.sha(P/p)==v for p,v in read(O/'replay.json')['stable_named_originals'].items())
    ar=B/'discovery-arithmetic-r136-parent';an=B/'discovery-analytic-r161-parent'
    for r,p in [('fresh-arithmetic-discovery-r136',ar),('arithmetic-r136-proof-r1',ar/'proof-r1-adoption'),('arithmetic-r136-contribution-r1',ar/'contribution-r1-adoption'),('arithmetic-r136-repair-r1',ar/'repair-r1-adoption'),('fresh-analytic-discovery-r161',an),('analytic-r161-proof-r1',an/'proof-r1-adoption'),('analytic-r161-contribution-r1',an/'contribution-r1-adoption'),('fresh-analytic-discovery-r166',B/'discovery-analytic-r166-parent')]:assert h.snap(B/r)==read(p/'observed-root.json')['root']
    assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
    files=read(O/'staging-allowlist.json')['files'];assert len(files)==len(set(files))==18 and len([p for p in files if'/fresh-structural-discovery-r174/'in p])==4 and not any('/private/'in p or '/controls/'in p or '/fresh-arithmetic-discovery-r137/'in p or p.endswith(('/observed-root.json','/replay.json'))for p in files)
    expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
    if mode=='prestage':
        assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+rel,prefix+'frontier/NEW-TEN-2026-10-14.md'}
        (O/'integration-validation.json').write_text(json.dumps({'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_head':head,'changed_existing_task_indices':[581],'new_task_indices':[584],'other_tasks_and_snapshot_fields_unchanged':True,'prior_source043_selection_reused_without_new_screen':True,'both_original_initial_review_guards_precede_new_root_brief_dispatch':True,'complete_original5570byte_suffix_preserved':True,'sealed_archive_arithmetic136_all_roots_closed_analytic161_and_analytic166_author_unchanged':True,'no_live_review_body_status_activity_read_poll_or_steer':True,'protected_bodies_named_metadata_nested_seals_local_unstaged':True,'journal_prefix_and_protected_unrelated_files_unchanged':True,'explicit_allowed_paths':18,'newAccepted':19,'remaining':1,'publication':'STOPPED','mathematical_gate_assigned':False},indent=2)+'\n')
    else:
        if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
        else:assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
        assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes()for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
    print(json.dumps({'phase':mode,'files':18,'tasks':585,'count':19,'sealed_roots_unchanged':True}))
if __name__=='__main__':main(sys.argv[1])
