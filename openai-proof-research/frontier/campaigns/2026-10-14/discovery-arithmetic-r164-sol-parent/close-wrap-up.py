from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent;R=B/'fresh-arithmetic-discovery-r164-sol';TP='frontier/campaigns/2026-10-14/tasks.json';JP='frontier/NEW-TEN-2026-10-14.md';CP='frontier/campaigns/2026-10-14/STOP-AFTER-CURRENT.json'
def git(*a,input=None):return subprocess.check_output(['git',*a],cwd=P,input=input)
def enc(x):return (json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode()
def sha(a):return hashlib.sha256(a).hexdigest()
def snap():
 out={}
 for p in R.rglob('*'):
  assert not p.is_symlink()
  if p.is_file():
   a=p.read_bytes();out[p.relative_to(R).as_posix()]={'bytes':len(a),'sha256':sha(a),'mode':p.stat().st_mode}
 return out
assert not git('diff','--cached','--name-only').strip();h=git('rev-parse','HEAD').decode().strip();ht=git('show',h+':openai-proof-research/'+TP);hj=git('show',h+':openai-proof-research/'+JP);wt=(P/TP).read_bytes();wj=(P/JP).read_bytes();wc=(P/CP).read_bytes();base=json.loads(ht);work=json.loads(wt);control=json.loads(wc)
assert len(base['tasks'])==len(work['tasks'])==863 and base['tasks'][862]==work['tasks'][862] and base['newAccepted']==work['newAccepted']==19
assert control['allowed_current_task_index']==862 and not control['new_research_delegations_allowed'] and not control['new_review_delegations_allowed']
term=json.loads((D/'task-status.json').read_bytes());intake=json.loads((D/'intake.json').read_bytes());verification=json.loads((D/'verification.json').read_bytes())
assert term['taskId']==base['tasks'][862]['taskId'] and term['status']=='completed' and not term['hasPendingChildRuns'] and term['pendingApproval'] is None
assert verification['status']=='MATCH' and snap()==json.loads((D/'private/intake/root-before.json').read_bytes())
now=datetime.now(timezone.utc).isoformat();control.update(mode='stopped',wrap_up_complete=True,stopped_utc=now,last_result='PREFREEZE_NO_NOMINEE',last_result_parent_assessment=str((D/'assessment.md').relative_to(P)),newAccepted=19,latestAcceptance='R041')
def update(original):
 x=copy.deepcopy(original);r=x['tasks'][862];r.update(term);r.update(disposition='PREFREEZE_NO_NOMINEE',observed_utc=now,theorem_frozen=False,diagnostic_frozen=False,correctness_gate=None,contribution_gate=None,accepted=False,count_change=0,parent_assessment=str((D/'assessment.md').relative_to(P)),parent_intake=str((D/'intake.json').relative_to(P)),artifact_verification=str((D/'verification.json').relative_to(P)),artifact_status='MATCH',author_inputs_unchanged=True,reading=intake['reading'],journal_scope_breach=intake['isolation_breach'],author_comparisons=intake['closed_author_comparisons'],unproved_directions=intake['unproved_directions'])
 x['operator_control']=copy.deepcopy(control);x['current_work_snapshot']['stop_after_current_20261025']=copy.deepcopy(control);x['current_work_snapshot']['r164_sol_final_disposition']={'task_index':862,'disposition':'PREFREEZE_NO_NOMINEE','count_change':0,'artifact_status':'MATCH','journal_scope_breach_disclosed':True,'research_stopped':True}
 assert [i for i,(a,b) in enumerate(zip(original['tasks'],x['tasks'])) if a!=b]==[862]
 assert all(x[k]==original[k] for k in original if k not in {'tasks','operator_control','current_work_snapshot'})
 return x
idx=enc(update(base));merged=enc(update(work));note=('\n\n### Current task wrapped; all research stopped — '+now+'\n\nR164-Sol is PREFREEZE/no nominee. [Parent assessment](campaigns/2026-10-14/discovery-arithmetic-r164-sol-parent/assessment.md) preserves the full exact-marginal correspondence-packing question,paid reductions and unresolved common-law requirement. Source22texts164770bytes;primary72pages across8partial PDFs,two visual checks. Journal breach[0,24000) versus authorized[4801,6347) explicitly retained;artifact checks do not repair it. Read-only verification MATCH69payloads11766107bytes72files15directories,24sourceblobs8trees8primaryPDFs5unchangedpairs,3wronganchor rejections. All sealed bytes/full modes unchanged. Per user request,wrap-up is complete and no further research/review/automatic next-round dispatch is authorized. Resume requires explicit user instruction. Count19/20,latestR041;publication/downstreamSTOPPED.\n').encode();ij=hj+note;mj=wj+note
foreign=[i for i,(a,b) in enumerate(zip(base['tasks'],work['tasks'])) if a!=b];(D/'wrap-up-record.json').write_bytes(enc({'head':h,'stopped_utc':now,'foreign_task_edits_preserved':foreign,'foreign_journal_preserved':wj!=hj,'changed_task':862,'new_tasks':0,'count_change':0,'research_stopped':True}))
protected={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
for n,s in protected.items():assert sha((P/n).read_bytes())==s
paths=[str((D/n).relative_to(P)) for n in ['task-status.json','assessment.md','intake.json','verification.json','verify-intake.py','close-wrap-up.py','wrap-up-record.json']]+[TP,JP,CP]
assert git('rev-parse','HEAD').decode().strip()==h and (P/TP).read_bytes()==wt and (P/JP).read_bytes()==wj and (P/CP).read_bytes()==wc
(P/TP).write_bytes(merged);(P/JP).write_bytes(mj);(P/CP).write_bytes(enc(control));subprocess.run(['git','add','--',*[n for n in paths if n not in {TP,JP}]],cwd=P,check=True)
for path,a in [(TP,idx),(JP,ij)]:
 blob=git('hash-object','-w','--stdin',input=a).decode().strip();subprocess.run(['git','update-index','--add','--cacheinfo','100644',blob,'openai-proof-research/'+path],cwd=P,check=True)
assert set(filter(None,git('diff','--cached','--name-only','-z').decode().split('\0')))=={'openai-proof-research/'+n for n in paths};subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
assert git('rev-parse','HEAD').decode().strip()==h and (P/TP).read_bytes()==merged and (P/JP).read_bytes()==mj
subprocess.run(['git','commit','-m','Preserve final correspondence-packing handoff and stop research'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip() and git('show','HEAD:openai-proof-research/'+TP)==idx and git('show','HEAD:openai-proof-research/'+JP)==ij and (P/TP).read_bytes()==merged and (P/JP).read_bytes()==mj
assert snap()==json.loads((D/'private/intake/root-before.json').read_bytes())
for n,s in protected.items():assert sha((P/n).read_bytes())==s
print(json.dumps({'commit':git('rev-parse','HEAD').decode().strip(),'research_stopped':True,'count':19,'new_tasks':0,'sealed_files_unchanged':True,'foreign_edits_preserved':foreign}))
