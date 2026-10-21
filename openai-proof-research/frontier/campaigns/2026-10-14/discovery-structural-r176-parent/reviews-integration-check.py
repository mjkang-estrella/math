#!/usr/bin/env python3
"""Entire immutable S176A review adoption; no new task or acceptance."""
import datetime,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2]
sp=importlib.util.spec_from_file_location('snapshot',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def main(mode):
    base=read(O/'reviews-integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
    if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
    rel=(B/'tasks.json').relative_to(P).as_posix();old=json.loads(git('show',head+':'+prefix+rel));new=read(B/'tasks.json');assert len(old['tasks'])==len(new['tasks'])==594 and [i for i in range(594)if old['tasks'][i]!=new['tasks'][i]]==[589,591,592]
    assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
    s0=old['current_work_snapshot'];s=new['current_work_snapshot'];assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','structural_r176_reviews','pending_terminal_intakes_20261021'} and set(s)-set(s0)=={'structural_r176_correctness_adoption','structural_r176_contribution_adoption','structural_r176_current_disposition'} and not set(s0)-set(s)
    assert not s['pending_terminal_intakes_20261021'] and s['t3_current_confirmed_running']==[new['tasks'][593]['taskId']] and s['fresh_discovery_current']==['fresh-analytic-discovery-r169'] and s['t3_dispatch_observations']==s0['t3_dispatch_observations']
    for i,role,verdict in [(591,'proof','INCOMPLETE'),(592,'contribution','TECHNICAL')]:
        out=O/(role+'-r1-adoption');root=B/('structural-r176-'+role+'-r1');a=read(out/'adoption.json');t=new['tasks'][i];raw=read(out/'task-status.json')['structuredContent'];assert all(t[k]==v for k,v in raw.items()) and t['review_verdict']==a['review_verdict']==verdict and not t['parent_intake_pending'] and t['entire_unchanged_frozen_scope'] and not t['accepted'] and t['count_change']==0
        assert t['parent_adoption']==(out/'adoption.json').relative_to(B).as_posix() and h.sha(out/'assessment.md')==a['parent_assessment_sha256'] and h.sha(root/'REVIEW.md')==a['review_sha256'] and s['structural_r176_'+('correctness'if role=='proof'else'contribution')+'_adoption']==a
        r=read(out/'replay.json');obs=read(out/'observed-root.json');assert r['payload_files']==(49 if role=='proof'else 75) and r['unchanged_original_inputs']==46 and h.snap(root)==obs['root'] and stat.S_IMODE(root.stat().st_mode)==obs['root_mode'] and all(h.sha(root/p)==v for p,v in r['anchors'].items())
        for p,x in r['stable_named_originals'].items():assert h.sha(P/p)==x['sha256'] and stat.S_IMODE((P/p).stat().st_mode)==x['mode']
        assert a['correctness']=='INCOMPLETE' and a['contribution']=='TECHNICAL' and a['correctness_condition']=='UNDISCHARGED' and a['no_established_counterexample_or_necessary_author_repair'] and a['no_desired_grade_retry_or_weaker_scope'] and not a['accepted'] and a['count_change']==0 and a['formalization']==a['manuscript']==a['local_release']=='NOT_STARTED_GATES_NOT_MET'
    t=new['tasks'][589];assert t['parent_disposition']=='FULL_SCOPE_CORRECTNESS_INCOMPLETE_CONTRIBUTION_TECHNICAL_CONDITIONAL' and t['scope_frozen'] and t['correctness']=='INCOMPLETE' and t['contribution']=='TECHNICAL' and t['contribution_correctness_condition']=='UNDISCHARGED' and not t['accepted'] and t['count_change']==0
    root=B/'fresh-structural-discovery-r176';assert h.sha(root/'STATEMENT.md')==t['frozen_scope_sha256']=='d31fdccc24ab795b16c233db8c6ac69dab4fa5a5a90597299e6a5c547b144621' and h.sha(root/'AUTHOR-PROOF.md')==t['author_proof_sha256']=='98e3e0c52eca762a8a7f32765b7d3a87b94a14040350ac14ab579de2b81adbba' and h.snap(root)==read(O/'observed-root.json')['root']
    ar=B/'discovery-arithmetic-r136-parent';an=B/'discovery-analytic-r161-parent';a166=B/'discovery-analytic-r166-parent'
    for r,p in [('fresh-arithmetic-discovery-r136',ar),('arithmetic-r136-proof-r1',ar/'proof-r1-adoption'),('arithmetic-r136-contribution-r1',ar/'contribution-r1-adoption'),('arithmetic-r136-repair-r1',ar/'repair-r1-adoption'),('fresh-analytic-discovery-r161',an),('analytic-r161-proof-r1',an/'proof-r1-adoption'),('analytic-r161-contribution-r1',an/'contribution-r1-adoption'),('fresh-analytic-discovery-r166',a166),('analytic-r166-contribution-r1',a166/'contribution-r1-adoption'),('analytic-r166-proof-r1',a166/'proof-r1-adoption'),('fresh-analytic-discovery-r168',B/'discovery-analytic-r168-parent'),('fresh-arithmetic-discovery-r139',B/'discovery-arithmetic-r139-parent')]:assert h.snap(B/r)==read(p/'observed-root.json')['root']
    assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
    files=read(O/'reviews-staging-allowlist.json')['files'];assert len(files)==len(set(files))==17 and not any('/private/'in p or '/controls/'in p or p.endswith(('/observed-root.json','/replay.json'))for p in files)
    expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
    if mode=='prestage':
        assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+rel,prefix+'frontier/NEW-TEN-2026-10-14.md'}
        (O/'reviews-integration-validation.json').write_text(json.dumps({'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_head':head,'changed_task_indices':[589,591,592],'other_tasks_and_snapshot_fields_unchanged':True,'entire_unchanged_scope_correctness_incomplete_contribution_technical':True,'correctness_condition_undischarged':True,'no_established_author_repair_counterexample_or_desired_grade_retry':True,'both_reviews_explicit_anchor_and46original_byte_mode_checks':True,'author_review_roots_and_prior_scopes_unchanged':True,'no_new_child_or_live_peer_body_status_activity_read_poll_or_steer':True,'private_bodies_named_metadata_nested_manifests_controls_local_unstaged':True,'journal_prefix_and_unrelated_protected_diffs_unchanged':True,'explicit_allowed_paths':17,'newAccepted':19,'remaining':1,'publication':'STOPPED'},indent=2)+'\n')
    else:
        if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
        else:assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
        assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes()for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
    print(json.dumps({'phase':mode,'files':17,'tasks':594,'count':19,'sealed_roots_unchanged':True}))
if __name__=='__main__':main(sys.argv[1])
