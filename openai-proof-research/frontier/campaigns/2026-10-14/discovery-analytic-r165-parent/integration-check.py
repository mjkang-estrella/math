#!/usr/bin/env python3
"""Bounded Analytic165 archive and Analytic166 launch integration checks."""
import datetime, importlib.util, json, stat, subprocess, sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2]
sp=importlib.util.spec_from_file_location('replay',O/'replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
def read(f):return json.loads(f.read_text())
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def main(mode):
    base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
    if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
    path=str((B/'tasks.json').relative_to(P));old=json.loads(git('show',head+':'+prefix+path));new=read(B/'tasks.json');assert len(old['tasks'])==580 and len(new['tasks'])==581 and [i for i in range(580)if old['tasks'][i]!=new['tasks'][i]]==[577]
    assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
    s0,s=old['current_work_snapshot'],new['current_work_snapshot'];assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','t3_current_confirmed_running','fresh_discovery_current','t3_dispatch_observations'} and set(s)-set(s0)=={'analytic_r165_archive','analytic166_prospective_isolation'} and not set(s0)-set(s)
    assert s['t3_dispatch_observations'][:-1]==s0['t3_dispatch_observations'] and not s['t3_last_polled_running'] and not s['pending_terminal_intakes_20261021'] and s['fresh_discovery_current']==['fresh-structural-discovery-r173','fresh-analytic-discovery-r166'] and s['t3_current_confirmed_running']==[new['tasks'][i]['taskId']for i in [578,579,580]]
    for i,n in [(577,'task-status.json'),(580,'analytic-r166-dispatch.json')]:assert all(new['tasks'][i][k]==v for k,v in read(O/n)['structuredContent'].items())
    t=new['tasks'][577];assert t['parent_disposition']=='PREFREEZE_NO_NOMINEE' and not t['scope_frozen'] and t['nominee'] is None and t['correctness']==t['contribution']=='UNREVIEWED' and not t['accepted'] and t['count_change']==0
    intake=read(O/'intake.json');assert s['analytic_r165_archive']==intake and h.sha(O/'assessment.md')==intake['assessment_sha256']
    t=new['tasks'][580];assert t['providerInstanceId']=='codex' and t['model']=='gpt-6-astra' and {x['id']:x['value']for x in t['options']}=={'reasoningEffort':'high','serviceTier':'default'} and t['status']=='running' and not t['hasPendingChildRuns'] and not t['hasPendingQuestion'] and t['pendingApproval'] is None and not t['accepted'] and t['count_change']==0 and t['source_family_navigation']==366
    receipt=read(O/'prospective-isolation.json');assert receipt['before_analytic166_brief_and_root'] and receipt['both_initial_guards_exclude_entire_analytic166_namespace'] and receipt['no_active_peer_body_status_activity_read_poll_or_steer']
    for e in receipt['existing_active_peer_original_initial_briefs']:
        peer=old['tasks'][e['task_index']];assert e['taskId']==peer['taskId'] and e['brief']==peer['brief'] and h.sha(B/e['brief'])==e['sha256']==peer['brief_sha256'] and e['literal_existing_exclusion'].encode()in(B/e['brief']).read_bytes()
    marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';text=(B/t['brief']).read_text();suffix=text.split(marker)[1];assert len(suffix.encode())==5570 and suffix==(B/'expanded-target-2026-10-17/fresh-analytic-r165-brief.txt').read_text().split(marker)[1] and h.sha(B/t['brief'])==t['brief_sha256']==receipt['new_brief']['sha256']==intake['brief_sha256']
    nav=read(O/'private/source366-navigation.json');tp=P/'sources/preprints-tree.json';tree=read(tp);assert h.sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b' and len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};assert len(nav['entries'])==9 and all(entries[e['path']]==e for e in nav['entries']) and next(e['path']for e in nav['entries']if e['path'].endswith('/build/main.tex'))in text
    n=read(O/'private/title-navigation.json');assert n['numeric_range']==[337,370] and n['title_only'] and not n['whole_map_decoded'] and len(n['families_selected'])==1 and n['families_selected'][0]['family']==366 and h.sha(P/'sources/CONTENTS.md')==n['catalogue_sha256'] and h.sha(O/'private/catalogue-366.md')==n['families_selected'][0]['selected_sha256']
    observed=read(O/'observed-root.json');root=B/'fresh-analytic-discovery-r165';assert h.snap(root)==observed['root'] and stat.S_IMODE(root.stat().st_mode)==observed['root_mode'] and all(h.sha(P/e['path'])==e['sha256']for e in read(O/'replay.json')['stable_named_originals'])
    ar=B/'discovery-arithmetic-r136-parent'
    for r,p in [('fresh-arithmetic-discovery-r136',ar),('arithmetic-r136-proof-r1',ar/'proof-r1-adoption'),('arithmetic-r136-contribution-r1',ar/'contribution-r1-adoption')]:assert h.snap(B/r)==read(p/'observed-root.json')['root']
    a=B/'discovery-analytic-r161-parent'
    for r,p in [('fresh-analytic-discovery-r161',a),('analytic-r161-proof-r1',a/'proof-r1-adoption'),('analytic-r161-contribution-r1',a/'contribution-r1-adoption')]:assert h.snap(B/r)==read(p/'observed-root.json')['root']
    assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and(P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
    files=read(O/'staging-allowlist.json')['files'];assert len(files)==len(set(files))==18 and len([p for p in files if'/fresh-analytic-discovery-r165/'in p])==4 and not any('/private/'in p or'/controls/'in p or'/fresh-analytic-discovery-r166/'in p or'/arithmetic-r136-repair-r1/'in p or p.endswith(('/observed-root.json','/replay.json'))for p in files)
    expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
    if mode=='prestage':
        assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+path,prefix+'frontier/NEW-TEN-2026-10-14.md'}
        (O/'integration-validation.json').write_text(json.dumps({'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_head':head,'changed_existing_task_indices':[577],'new_task_indices':[580],'other_tasks_and_snapshot_fields_unchanged':True,'initial_peer_guards_precede_new_brief_root_dispatch':True,'complete_original5570byte_suffix_preserved':True,'source366_main_and_includes_metadata_confirmed':True,'sealed_archive_arithmetic136_author_both_reviews_and_closed_analytic161_roots_unchanged':True,'protected_bodies_private_seals_identity_replay_metadata_local_unstaged':True,'journal_prefix_and_protected_unrelated_files_unchanged':True,'explicit_allowed_paths':18,'newAccepted':19,'remaining':1,'publication':'STOPPED','mathematical_gate_assigned':False},indent=2)+'\n')
    else:
        if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
        else:assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
        assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes()for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
    print(json.dumps({'phase':mode,'files':18,'tasks':581,'count':19,'sealed_roots_unchanged':True}))
if __name__=='__main__':main(sys.argv[1])
