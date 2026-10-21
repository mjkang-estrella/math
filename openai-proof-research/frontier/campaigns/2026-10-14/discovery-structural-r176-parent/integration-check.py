#!/usr/bin/env python3
"""Narrow two-terminal intake and first S176A review dispatch integration."""
import datetime,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'discovery-analytic-r168-parent'
sp=importlib.util.spec_from_file_location('replay',A/'replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def main(mode):
    base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
    if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
    rel=(B/'tasks.json').relative_to(P).as_posix();old=json.loads(git('show',head+':'+prefix+rel));new=read(B/'tasks.json')
    assert len(old['tasks'])==591 and len(new['tasks'])==593 and [i for i in range(591)if old['tasks'][i]!=new['tasks'][i]]==[588,589]
    assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
    s0=old['current_work_snapshot'];s=new['current_work_snapshot']
    assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','t3_current_confirmed_running','fresh_discovery_current','t3_dispatch_observations'} and set(s)-set(s0)=={'analytic_r168_archive','structural_r176_intake','structural_r176_reviews','structural176_review_prospective_isolation','analytic169_preparation_deferred'} and not set(s0)-set(s)
    assert s['t3_dispatch_observations'][:-2]==s0['t3_dispatch_observations'] and not s['pending_terminal_intakes_20261021'] and not s['t3_last_polled_running'] and s['fresh_discovery_current']==['fresh-arithmetic-discovery-r139'] and s['t3_current_confirmed_running']==[new['tasks'][i]['taskId']for i in [590,591,592]]
    for i,o,n in [(588,A,'task-status.json'),(589,O,'task-status.json'),(591,O,'proof-r1-dispatch.json'),(592,O,'contribution-r1-dispatch.json')]:assert all(new['tasks'][i][k]==v for k,v in read(o/n)['structuredContent'].items())
    ia=read(A/'intake.json');ins=read(O/'intake.json');assert s['analytic_r168_archive']==ia and s['structural_r176_intake']==ins and s['structural_r176_reviews']==ins['reviews']
    assert h.sha(A/'assessment.md')==ia['assessment_sha256'] and h.sha(O/'assessment.md')==ins['assessment_sha256'] and h.sha(O/'questions.md')==ins['questions_sha256']
    ta=new['tasks'][588];ts=new['tasks'][589]
    assert ta['parent_disposition']=='PREFREEZE_NO_NOMINEE' and not ta['scope_frozen'] and ta['nominee']is None and ta['correctness']==ta['contribution']=='UNREVIEWED'
    assert ts['parent_disposition']=='FULL_AUTHOR_PROOF_NOMINEE_INDEPENDENT_REVIEWS_PENDING' and ts['scope_frozen'] and ts['nominee']=='S176A' and ts['correctness']==ts['contribution']=='UNREVIEWED' and ts['review_task_indices']==[591,592]
    assert all(not new['tasks'][i]['accepted'] and new['tasks'][i]['count_change']==0 for i in [588,589,591,592])
    root=B/'fresh-structural-discovery-r176';assert h.sha(root/'STATEMENT.md')==ins['frozen_scope_sha256']=='d31fdccc24ab795b16c233db8c6ac69dab4fa5a5a90597299e6a5c547b144621' and h.sha(root/'AUTHOR-PROOF.md')==ins['author_proof_sha256']=='98e3e0c52eca762a8a7f32765b7d3a87b94a14040350ac14ab579de2b81adbba'
    original=(B/'expanded-target-2026-10-17/fresh-structural-r176-brief.txt').read_text();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';assert len(original.split(marker)[1].encode())==5570
    for i,role in [(591,'proof'),(592,'contribution')]:
        t=new['tasks'][i];assert t['providerInstanceId']=='codex' and t['model']=='gpt-6-astra' and {x['id']:x['value']for x in t['options']}=={'reasoningEffort':'high','serviceTier':'default'} and t['status']=='running' and not t['hasPendingChildRuns'] and not t['hasPendingQuestion'] and t['pendingApproval']is None and t['nominee']=='S176A'
        text=(B/t['brief']).read_text();assert h.sha(B/t['brief'])==t['brief_sha256'] and original in text and (root/'STATEMENT.md').read_text()in text and (root/'AUTHOR-PROOF.md').read_text()in text and (root/'private/reading-record.md').read_text()in text and (root/'private/operative-comparison.md').read_text()in text and (O/'questions.md').read_text()in text
        sibling='structural-r176-'+('contribution'if role=='proof'else'proof')+'-r1';assert sibling in text.split('--- COMPLETE ORIGINAL AUTHOR TASK BRIEF ---')[0] and '*arithmetic*r139*'in text and '*structural*r176*'in text
    pro=read(O/'prospective-isolation.json');e=pro['active_peer_original_initial_brief'];assert pro['before_both_review_roots_and_briefs'] and pro['entire_structural176_namespace_initially_excluded'] and pro['both_initial_briefs_mutually_exclude_siblings'] and pro['no_live_peer_body_status_activity_read_poll_or_steer'] and e['task_index']==590 and e['taskId']==old['tasks'][590]['taskId'] and h.sha(B/e['brief'])==e['sha256']==old['tasks'][590]['brief_sha256'] and e['literal_existing_exclusion'].encode()in(B/e['brief']).read_bytes()
    assert not(B/'fresh-analytic-discovery-r169').exists() and not(B/'expanded-target-2026-10-17/fresh-analytic-r169-brief.txt').exists() and s['analytic169_preparation_deferred']['no_new_root_brief_task']
    for o,r in [(A,'fresh-analytic-discovery-r168'),(O,'fresh-structural-discovery-r176')]:
        obs=read(o/'observed-root.json');assert h.snap(B/r)==obs['root'] and stat.S_IMODE((B/r).stat().st_mode)==obs['root_mode'];rr=read(o/'replay.json');assert all(h.sha(P/p)==v for p,v in rr['stable_named_originals'].items()) and all(h.sha(P/p)==v for p,v in rr['completed_original_closing_hashes_only'].items())
    ar=B/'discovery-arithmetic-r136-parent';an=B/'discovery-analytic-r161-parent';a166=B/'discovery-analytic-r166-parent'
    for r,p in [('fresh-arithmetic-discovery-r136',ar),('arithmetic-r136-proof-r1',ar/'proof-r1-adoption'),('arithmetic-r136-contribution-r1',ar/'contribution-r1-adoption'),('arithmetic-r136-repair-r1',ar/'repair-r1-adoption'),('fresh-analytic-discovery-r161',an),('analytic-r161-proof-r1',an/'proof-r1-adoption'),('analytic-r161-contribution-r1',an/'contribution-r1-adoption'),('fresh-analytic-discovery-r166',a166),('analytic-r166-contribution-r1',a166/'contribution-r1-adoption'),('analytic-r166-proof-r1',a166/'proof-r1-adoption')]:assert h.snap(B/r)==read(p/'observed-root.json')['root']
    assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
    files=read(O/'staging-allowlist.json')['files'];assert len(files)==len(set(files))==33 and not any('/private/'in p or '/controls/'in p or p.endswith(('/observed-root.json','/replay.json'))or'/structural-r176-proof-r1/'in p or'/structural-r176-contribution-r1/'in p for p in files)
    expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
    if mode=='prestage':
        assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+rel,prefix+'frontier/NEW-TEN-2026-10-14.md'}
        (O/'integration-validation.json').write_text(json.dumps({'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_head':head,'changed_existing_task_indices':[588,589],'new_review_indices':[591,592],'other_tasks_and_snapshot_fields_unchanged':True,'analytic168_prefreeze_no_nominee':True,'s176a_entire_immutable_author_proof_submitted_to_both_independent_reviews':True,'original_initial_peer_guard_and_mutual_review_guards':True,'complete_original_author_brief_scope_proof_comparison_limits_questions_in_both_prompts':True,'both_codex_astra_high_default_actual_dispatches':True,'sealed_roots_and_closed_prior_scopes_unchanged':True,'analytic169_preparation_deferred_no_new_root_brief_task':True,'protected_bodies_named_metadata_controls_nested_envelopes_local_unstaged':True,'journal_prefix_and_protected_unrelated_files_unchanged':True,'explicit_allowed_paths':33,'newAccepted':19,'remaining':1,'publication':'STOPPED','mathematical_gate_assigned':False},indent=2)+'\n')
    else:
        if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
        else:assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
        assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes()for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
    print(json.dumps({'phase':mode,'files':33,'tasks':593,'count':19,'sealed_roots_unchanged':True}))
if __name__=='__main__':main(sys.argv[1])
