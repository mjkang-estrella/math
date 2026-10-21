#!/usr/bin/env python3
"""Narrow A169 prefreeze archive and three actual mutually guarded discoveries."""
import datetime,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2]
sp=importlib.util.spec_from_file_location('replay',O/'replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def main(mode):
    base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
    if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
    rel=(B/'tasks.json').relative_to(P).as_posix();old=json.loads(git('show',head+':'+prefix+rel));new=read(B/'tasks.json');assert len(old['tasks'])==594 and len(new['tasks'])==597 and [i for i in range(594)if old['tasks'][i]!=new['tasks'][i]]==[593]
    assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
    s0=old['current_work_snapshot'];s=new['current_work_snapshot'];assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','t3_current_confirmed_running','fresh_discovery_current','t3_dispatch_observations'} and set(s)-set(s0)=={'analytic_r169_archive','fresh170177140_prospective_isolation'} and not set(s0)-set(s)
    assert s['t3_dispatch_observations'][:-3]==s0['t3_dispatch_observations'] and not s['pending_terminal_intakes_20261021'] and not s['t3_last_polled_running'] and s['t3_current_confirmed_running']==[new['tasks'][i]['taskId']for i in [594,595,596]] and s['fresh_discovery_current']==[new['tasks'][i]['output']for i in [594,595,596]]
    assert all(new['tasks'][593][k]==v for k,v in read(O/'task-status.json')['structuredContent'].items());t=new['tasks'][593];assert t['parent_disposition']=='PREFREEZE_NO_NOMINEE' and not t['scope_frozen'] and t['nominee']is None and t['correctness']==t['contribution']=='UNREVIEWED' and not t['accepted'] and t['count_change']==0
    intake=read(O/'intake.json');assert s['analytic_r169_archive']==intake and h.sha(O/'assessment.md')==intake['assessment_sha256']
    pro=read(O/'prospective-isolation.json');assert pro['before_all_three_roots_and_briefs'] and pro['all_previous_children_notified_terminal'] and not pro['existing_active_peers'] and pro['all_mutual_guards_in_all_initial_briefs_before_first_dispatch'] and pro['no_live_peer_body_status_activity_read_poll_or_steer'] and len(pro['actual_dispatches'])==3
    marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';original=(B/'expanded-target-2026-10-17/fresh-analytic-r169-brief.txt').read_text().split(marker)[1];assert len(original.encode())==5570
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(tree['tree'])==13223 and not tree['truncated'] and h.sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    for i,lane,n,family,objects,folders in [(594,'analytic',170,300,22,2),(595,'structural',177,314,11,1),(596,'arithmetic',140,39,49,4)]:
        t=new['tasks'][i];name=f'fresh-{lane}-r{n}';raw=read(O/(name+'-dispatch.json'))['structuredContent'];assert all(t[k]==v for k,v in raw.items()) and t['providerInstanceId']=='codex' and t['model']=='gpt-6-astra' and {x['id']:x['value']for x in t['options']}=={'reasoningEffort':'high','serviceTier':'default'} and t['status']=='running' and not t['hasPendingChildRuns'] and not t['hasPendingQuestion'] and t['pendingApproval']is None and not t['accepted'] and t['count_change']==0 and t['source_family_navigation']==family
        p=B/t['brief'];text=p.read_text();assert text.split(marker)[1]==original and h.sha(p)==t['brief_sha256']==pro['prepared_briefs'][i-594]['brief_sha256'] and all(x in text for x in ['*analytic*r170*','*structural*r177*','*arithmetic*r140*'])
        nav=read(O/f'private/source{family}-navigation.json');selection=read(O/f'private/source{family}-selection.json');titles=read(O/'private'/selection['title_navigation_record']);assert len(nav['entries'])==objects and len(nav['family_manuscript_folders'])==folders and all(lookup[e['path']]==e for e in nav['entries']) and not nav['parent_read_source_proofs'] and selection['only_one_family_body_selected_for_lane'] and titles['title_only'] and not titles['whole_map_decoded'] and any(e['family']==family for e in titles['titles'])
        assert h.sha(O/f'private/catalogue-{family}.md')==selection['sha256'] and f"[{selection['start']},{selection['end']})"in text
        mains=[e for e in nav['entries']if e['path'].endswith(('/main.tex','/paper.tex'))];assert mains and all(e['path']in text for e in mains)
    obs=read(O/'observed-root.json');assert h.snap(B/'fresh-analytic-discovery-r169')==obs['root'] and stat.S_IMODE((B/'fresh-analytic-discovery-r169').stat().st_mode)==obs['root_mode']
    replay=read(O/'replay.json');assert all(h.sha(P/p)==v for p,v in replay['stable_named_originals'].items())
    for x in replay['direct_ranges']:
        with(P/x['path']).open('rb')as f:f.seek(x['start']);data=f.read(x['end']-x['start'])
        import hashlib
        assert hashlib.sha256(data).hexdigest()==x['sha256']
    ar=B/'discovery-arithmetic-r136-parent';an=B/'discovery-analytic-r161-parent';a166=B/'discovery-analytic-r166-parent';s176=B/'discovery-structural-r176-parent'
    for r,p in [('fresh-arithmetic-discovery-r136',ar),('arithmetic-r136-proof-r1',ar/'proof-r1-adoption'),('arithmetic-r136-contribution-r1',ar/'contribution-r1-adoption'),('arithmetic-r136-repair-r1',ar/'repair-r1-adoption'),('fresh-analytic-discovery-r161',an),('analytic-r161-proof-r1',an/'proof-r1-adoption'),('analytic-r161-contribution-r1',an/'contribution-r1-adoption'),('fresh-analytic-discovery-r166',a166),('analytic-r166-contribution-r1',a166/'contribution-r1-adoption'),('analytic-r166-proof-r1',a166/'proof-r1-adoption'),('fresh-analytic-discovery-r168',B/'discovery-analytic-r168-parent'),('fresh-arithmetic-discovery-r139',B/'discovery-arithmetic-r139-parent'),('fresh-structural-discovery-r176',s176),('structural-r176-proof-r1',s176/'proof-r1-adoption'),('structural-r176-contribution-r1',s176/'contribution-r1-adoption')]:assert h.snap(B/r)==read(p/'observed-root.json')['root']
    assert new['tasks'][589]['correctness']=='INCOMPLETE' and new['tasks'][589]['contribution']=='TECHNICAL' and new['tasks'][589]['contribution_correctness_condition']=='UNDISCHARGED'
    assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
    files=read(O/'staging-allowlist.json')['files'];assert len(files)==len(set(files))==27 and not any('/private/'in p or '/controls/'in p or p.endswith(('/observed-root.json','/replay.json'))or any('/'+new['tasks'][i]['output']+'/'in p for i in [594,595,596])for p in files)
    expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
    if mode=='prestage':
        assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+rel,prefix+'frontier/NEW-TEN-2026-10-14.md'}
        (O/'integration-validation.json').write_text(json.dumps({'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_head':head,'changed_existing_task_indices':[593],'new_task_indices':[594,595,596],'other_tasks_and_snapshot_fields_unchanged':True,'analytic169_prefreeze_no_nominee':True,'three_distinct_confirmed_families_one_body_each':True,'canonical_metadata_counts':[22,11,49],'all_initial_mutual_guards_before_first_dispatch_no_preexisting_active_peers':True,'complete_original5570byte_suffix_in_all_briefs':True,'actual_codex_astra_high_default_dispatches':True,'author_archive_prior_scopes_and_both_s176a_reviews_unchanged':True,'s176a_correctness_incomplete_conditional_technical_undischarged':True,'protected_bodies_named_metadata_private_preparation_controls_unstaged':True,'journal_prefix_and_unrelated_protected_diffs_unchanged':True,'explicit_allowed_paths':27,'newAccepted':19,'remaining':1,'publication':'STOPPED','mathematical_gate_assigned':False},indent=2)+'\n')
    else:
        if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
        else:assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
        assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes()for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
    print(json.dumps({'phase':mode,'files':27,'tasks':597,'count':19,'sealed_roots_unchanged':True}))
if __name__=='__main__':main(sys.argv[1])
