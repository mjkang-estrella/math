#!/usr/bin/env python3
"""Bounded NEEDS_REPAIR adoption and first exact-scope response launch checks."""
import datetime, importlib.util, json, stat, subprocess, sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parents[1];P=B.parents[2]
sp=importlib.util.spec_from_file_location('replay',O/'replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
def read(f):return json.loads(f.read_text())
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def main(mode):
    base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
    if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
    path=str((B/'tasks.json').relative_to(P));old=json.loads(git('show',head+':'+prefix+path));new=read(B/'tasks.json');assert len(old['tasks'])==579 and len(new['tasks'])==580 and [i for i in range(579)if old['tasks'][i]!=new['tasks'][i]]==[571,575,576]
    assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
    assert {k for k in old['tasks'][576]if old['tasks'][576][k]!=new['tasks'][576][k]}=={'correctness_condition'}
    s0,s=old['current_work_snapshot'],new['current_work_snapshot'];assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','t3_current_confirmed_running','t3_dispatch_observations','arithmetic_r136_reviews'} and set(s)-set(s0)=={'arithmetic_r136_correctness_adoption','arithmetic_r136_repair','arithmetic136_repair_prospective_isolation'} and not set(s0)-set(s)
    assert s['t3_dispatch_observations'][:-1]==s0['t3_dispatch_observations'] and not s['pending_terminal_intakes_20261021'] and not s['t3_last_polled_running'] and s['fresh_discovery_current']==s0['fresh_discovery_current']==['fresh-analytic-discovery-r165','fresh-structural-discovery-r173'] and s['t3_current_confirmed_running']==[new['tasks'][i]['taskId']for i in [577,578,579]]
    review=new['tasks'][575];assert all(review[k]==v for k,v in read(O/'task-status.json')['structuredContent'].items()) and review['review_verdict']=='NEEDS_REPAIR' and review['parent_adopted_correctness'] and review['entire_unchanged_frozen_scope'] and not review['accepted'] and review['count_change']==0
    nominee=new['tasks'][571];assert nominee['correctness']=='NEEDS_REPAIR' and nominee['contribution']=='INCOMPLETE' and nominee['parent_disposition']=='FULL_AUTHOR_PROOF_NEEDS_FULL_SCOPE_REPAIR' and not nominee['accepted'] and nominee['count_change']==0
    adoption=read(O/'adoption.json');assert s['arithmetic_r136_correctness_adoption']==adoption and adoption['review_verdict']=='NEEDS_REPAIR' and adoption['contribution']=='INCOMPLETE' and not adoption['review_retry_dispatched'] and adoption['first_substantive_author_response'] and h.sha(O/'assessment.md')==adoption['parent_assessment_sha256']
    assert s['arithmetic_r136_reviews']['correctness']['verdict']=='NEEDS_REPAIR' and s['arithmetic_r136_reviews']['contribution']['verdict']=='INCOMPLETE' and s['arithmetic_r136_reviews']['contribution']['correctness_condition']=='NOT_DISCHARGED_CORRECTNESS_NEEDS_REPAIR' and all(s['arithmetic_r136_reviews'][k]=='NOT_STARTED_GATES_NOT_MET'for k in ['formalization','manuscript','local_release'])
    receipt=read(O/'prospective-isolation.json');prep=read(O/'repair-preparation.json');assert receipt['before_arithmetic136_repair_root_and_brief'] and receipt['both_initial_peer_guards_cover_entire_arithmetic136_repair_namespace'] and receipt['no_live_peer_body_status_activity_read_poll_or_steer'] and receipt['repair_preparation']==prep
    for e in receipt['existing_active_peer_original_initial_briefs']:
        peer=old['tasks'][e['task_index']];assert e['taskId']==peer['taskId'] and e['brief']==peer['brief'] and h.sha(B/e['brief'])==e['sha256']==peer['brief_sha256'] and e['literal_existing_exclusion'].encode()in(B/e['brief']).read_bytes()
    dispatch=read(O/'repair-r1-dispatch.json');t=new['tasks'][579];assert all(t[k]==v for k,v in dispatch['structuredContent'].items()) and s['t3_dispatch_observations'][-1]==dispatch and t['providerInstanceId']=='codex' and t['model']=='gpt-6-astra' and {x['id']:x['value']for x in t['options']}=={'reasoningEffort':'high','serviceTier':'default'} and t['status']=='running' and not t['hasPendingChildRuns'] and not t['hasPendingQuestion'] and t['pendingApproval'] is None and not t['accepted'] and t['count_change']==0 and t['role']=='research' and t['research_kind']=='exact-scope author repair'
    text=(B/t['brief']).read_bytes();assert h.sha(B/t['brief'])==t['brief_sha256']==prep['brief_sha256']==adoption['repair_brief_sha256'] and len(text)==prep['brief_bytes'] and not prep['prior_author_response'] and prep['first_substantive_repair_not_review_retry']
    author=B/'fresh-arithmetic-discovery-r136';contribution=B/'arithmetic-r136-contribution-r1';correctness=B/'arithmetic-r136-proof-r1';original=B/'expanded-target-2026-10-17/fresh-arithmetic-r136-brief.txt'
    for f,value in [(original,prep['complete_original_author_brief_sha256']),(author/'FROZEN.md',prep['frozen_scope_sha256']),(correctness/'notes/review.md',prep['correctness_findings_sha256']),(contribution/'review.md',prep['contribution_findings_sha256'])]:assert h.sha(f)==value and f.read_bytes()in text
    assert (O.parent/'preflight.md').read_bytes()in text and b'*analytic*r165*'in text and b'*structural*r173*'in text and h.sha(author/'notes/author-proof.md')==prep['original_proof_sha256']==adoption['original_author_proof_sha256']
    observed=read(O/'observed-root.json');assert h.snap(correctness)==observed['root'] and stat.S_IMODE(correctness.stat().st_mode)==observed['root_mode'] and all(h.sha(P/e['path'])==e['sha256']for e in read(O/'replay.json')['stable_named_originals'])
    assert h.snap(author)==read(O.parent/'observed-root.json')['root'] and h.snap(contribution)==read(O.parent/'contribution-r1-adoption/observed-root.json')['root']
    a=B/'discovery-analytic-r161-parent'
    for r,p in [('fresh-analytic-discovery-r161',a),('analytic-r161-proof-r1',a/'proof-r1-adoption'),('analytic-r161-contribution-r1',a/'contribution-r1-adoption')]:assert h.snap(B/r)==read(p/'observed-root.json')['root']
    assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and(P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
    files=read(O/'staging-allowlist.json')['files'];assert len(files)==len(set(files))==20 and len([p for p in files if'/arithmetic-r136-proof-r1/'in p])==5 and not any('/private/'in p or'/controls/'in p or'/arithmetic-r136-repair-r1/'in p or p.endswith(('/observed-root.json','/replay.json','/finite-certificate.json'))for p in files)
    expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
    if mode=='prestage':
        assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+path,prefix+'frontier/NEW-TEN-2026-10-14.md'}
        (O/'integration-validation.json').write_text(json.dumps({'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_head':head,'changed_existing_task_indices':[571,575,576],'new_exact_scope_repair_task_index':579,'other_tasks_and_snapshot_fields_unchanged':True,'entire_unchanged_scope_correctness_NEEDS_REPAIR_adopted':True,'contribution_INCOMPLETE_correctness_condition_not_discharged':True,'both_complete_findings_original_task_and_frozen_statement_embedded_in_first_response_task':True,'no_review_retry_weaker_scope_or_downstream_gate':True,'initial_peer_guards_precede_repair_root_brief_dispatch':True,'author_both_reviews_and_closed_analytic161_roots_unchanged':True,'protected_bodies_identity_replay_and_finite_metadata_local_unstaged':True,'journal_prefix_and_protected_unrelated_files_unchanged':True,'explicit_allowed_paths':20,'newAccepted':19,'remaining':1,'publication':'STOPPED','acceptance_or_count_assigned':False},indent=2)+'\n')
    else:
        if mode=='staged':
            actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':'
            whitespace=subprocess.run(['git','diff','--cached','--check'],cwd=P,capture_output=True,text=True)
            # The already-dispatched prompt deliberately retains complete embedded text and one separator newline.
            expected_eof=prefix+str((B/prep['brief']).relative_to(P))+':468: new blank line at EOF.\n'
            assert whitespace.returncode==2 and whitespace.stdout==expected_eof and not whitespace.stderr
            subprocess.run(['git','-c','core.whitespace=-blank-at-eof','diff','--cached','--check'],cwd=P,check=True)
        else:assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
        assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes()for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
    print(json.dumps({'phase':mode,'files':20,'tasks':580,'count':19,'sealed_roots_unchanged':True,'correctness':'NEEDS_REPAIR'}))
if __name__=='__main__':main(sys.argv[1])
