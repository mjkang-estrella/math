#!/usr/bin/env python3
"""Narrow author intake and two actual mutually isolated full-scope review dispatches."""
import datetime,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2]
sp=importlib.util.spec_from_file_location('replay',O/'replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def git(*args):return subprocess.check_output(['git',*args],cwd=P)
def main(mode):
    base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
    if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
    rel=(B/'tasks.json').relative_to(P).as_posix();old=json.loads(git('show',head+':'+prefix+rel));new=read(B/'tasks.json');assert len(old['tasks'])==582 and len(new['tasks'])==584 and [i for i in range(582)if old['tasks'][i]!=new['tasks'][i]]==[580]
    assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
    s0=old['current_work_snapshot'];s=new['current_work_snapshot'];assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','t3_current_confirmed_running','pending_terminal_intakes_20261021','t3_dispatch_observations'} and set(s)-set(s0)=={'analytic_r166_intake','analytic_r166_reviews','analytic166_review_prospective_isolation'} and not set(s0)-set(s)
    intake=read(O/'intake.json');assert s['analytic_r166_intake']==intake and s['analytic_r166_reviews']==intake['reviews'] and s['t3_dispatch_observations'][:-2]==s0['t3_dispatch_observations'] and s['t3_dispatch_observations'][-2:]==intake['reviews'] and not s['pending_terminal_intakes_20261021'] and not s['t3_last_polled_running'] and s['fresh_discovery_current']==['fresh-structural-discovery-r174'] and s['t3_current_confirmed_running']==[new['tasks'][i]['taskId']for i in [581,582,583]]
    assert intake['correctness']==intake['contribution']=='PENDING_INDEPENDENT_REVIEW' and not intake['accepted'] and intake['count_change']==0 and h.sha(O/'assessment.md')==intake['assessment_sha256'] and h.sha(O/'preflight.md')==intake['preflight_sha256']
    a=B/'fresh-analytic-discovery-r166';obs=read(O/'observed-root.json');assert h.snap(a)==obs['root'] and stat.S_IMODE(a.stat().st_mode)==obs['root_mode'] and h.sha(a/'STATEMENT.md')==intake['frozen_scope_sha256']=='c518b1e730585463899f83a6c1aa1023717817671ecdcd540245024745a1cd33' and h.sha(a/'PROOF.md')==intake['author_proof_sha256']=='5a5877d58132597566ba6fed1cd376501810dc4294270c84f14b3d65325a8828'
    stable=read(O/'replay.json')['stable_named_originals'];assert stable['frontier/NEW-TEN-2026-10-14.md']==base['journal_sha256'] and all(h.sha(P/p)==v for p,v in stable.items()if p!='frontier/NEW-TEN-2026-10-14.md')
    for e in read(a/'private/direct-originals.json')['objects']:
        if e['original']=='frontier/NEW-TEN-2026-10-14.md':
            with (P/e['original']).open('rb')as f:f.seek(e['start']);data=f.read(e['end']-e['start'])
            assert data==(a/e['selected']).read_bytes()
    pro=read(O/'prospective-isolation.json');assert pro['before_both_review_roots_and_briefs'] and pro['entire_author_review_parent_brief_namespace_covered'] and pro['no_active_peer_body_status_activity_read_poll_or_steer']
    e=pro['active_peer_original_initial_brief'];peer=old['tasks'][e['task_index']];assert e['taskId']==peer['taskId'] and h.sha(B/e['brief'])==e['sha256']==peer['brief_sha256'] and e['literal_existing_exclusion'].encode()in(B/e['brief']).read_bytes()
    for i,name,kind in [(582,'proof','correctness'),(583,'contribution','substantial-contribution')]:
        t=new['tasks'][i];raw=read(O/(name+'-dispatch.json'))['structuredContent'];assert all(t[k]==v for k,v in raw.items()) and t['status']=='running' and t['providerInstanceId']=='codex' and t['model']=='gpt-6-astra' and {x['id']:x['value']for x in t['options']}=={'reasoningEffort':'high','serviceTier':'default'} and not t['hasPendingChildRuns'] and not t['hasPendingQuestion'] and t['pendingApproval'] is None and t['review_kind']==kind and not t['accepted'] and t['count_change']==0
        record=next(e for e in pro['new_reviews']if e['role']==kind);f=B/t['brief'];text=f.read_text();assert h.sha(f)==t['brief_sha256']==record['sha256'] and len(f.read_bytes())==record['bytes'] and (B/'expanded-target-2026-10-17/fresh-analytic-r166-brief.txt').read_text()in text and (a/'STATEMENT.md').read_text()in text and (a/'PROOF.md').read_text()in text and (O/'preflight.md').read_text()in text and '*analytic*r166*'in text and '*structural*r174*'in text
    ar=B/'discovery-arithmetic-r136-parent';an=B/'discovery-analytic-r161-parent'
    for r,p in [('fresh-arithmetic-discovery-r136',ar),('arithmetic-r136-proof-r1',ar/'proof-r1-adoption'),('arithmetic-r136-contribution-r1',ar/'contribution-r1-adoption'),('arithmetic-r136-repair-r1',ar/'repair-r1-adoption'),('fresh-analytic-discovery-r161',an),('analytic-r161-proof-r1',an/'proof-r1-adoption'),('analytic-r161-contribution-r1',an/'contribution-r1-adoption')]:assert h.snap(B/r)==read(p/'observed-root.json')['root']
    assert not (B/'fresh-arithmetic-discovery-r137').exists() and not (B/'expanded-target-2026-10-17/fresh-arithmetic-r137-brief.txt').exists() and all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
    files=read(O/'staging-allowlist.json')['files'];assert len(files)==len(set(files))==24 and len([p for p in files if '/fresh-analytic-discovery-r166/'in p])==6 and not any('/private/'in p or '/controls/'in p or '/analytic-r166-proof-r1/'in p or '/analytic-r166-contribution-r1/'in p or p.endswith(('/observed-root.json','/replay.json'))for p in files)
    expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
    if mode=='prestage':
        assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+rel,prefix+'frontier/NEW-TEN-2026-10-14.md'}
        (O/'integration-validation.json').write_text(json.dumps({'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_head':head,'changed_existing_task_indices':[580],'new_task_indices':[582,583],'other_tasks_and_snapshot_fields_unchanged':True,'complete_original_author_brief_statement_proof_limits_questions_in_both_prompts':True,'both_actual_review_dispatches':'codex/gpt-6-astra/high/default','mutual_initial_guards_precede_dispatch':True,'sealed_author_root_and_all_prior_closed_roots_unchanged':True,'no_mathematical_gate_or_count_assigned':True,'arithmetic137_deferred_for_review_capacity':True,'protected_bodies_nested_manifest_identity_metadata_local_unstaged':True,'journal_prefix_and_protected_unrelated_files_unchanged':True,'explicit_allowed_paths':24,'newAccepted':19,'remaining':1,'publication':'STOPPED'},indent=2)+'\n')
    else:
        if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
        else:assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
        assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes()for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
    print(json.dumps({'phase':mode,'files':24,'tasks':584,'count':19,'sealed_roots_unchanged':True}))
if __name__=='__main__':main(sys.argv[1])
