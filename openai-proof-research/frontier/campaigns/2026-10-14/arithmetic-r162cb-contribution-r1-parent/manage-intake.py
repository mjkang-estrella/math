#!/usr/bin/env python3
"""Adopt conditional contribution assessment without touching the pending review."""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
R=B/'arithmetic-r162cb-contribution-r1';TP='frontier/campaigns/2026-10-14/tasks.json';JP='frontier/NEW-TEN-2026-10-14.md'
def git(*args,input=None):return subprocess.check_output(['git',*args],cwd=P,input=input)
def sha(a):return hashlib.sha256(a).hexdigest()
def enc(x):return (json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode()
def snap(root):
 out={}
 for p in root.rglob('*'):
  assert not p.is_symlink()
  if p.is_file():
   a=p.read_bytes();out[p.relative_to(root).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=p.stat().st_mode)
 return out
assert not git('diff','--cached','--name-only').strip()
h=git('rev-parse','HEAD').decode().strip();ht=git('show',h+':openai-proof-research/'+TP);hj=git('show',h+':openai-proof-research/'+JP)
wt=(P/TP).read_bytes();wj=(P/JP).read_bytes();assert wj==hj
base=json.loads(ht);work=json.loads(wt);assert len(base['tasks'])==len(work['tasks'])
assert all(base['tasks'][i]==work['tasks'][i] for i in [837,838,839])
assert base['newAccepted']==work['newAccepted']==19 and base['latestAcceptance']==work['latestAcceptance']=='R041'
foreign=[i for i,(a,b) in enumerate(zip(base['tasks'],work['tasks'])) if a!=b];foreign_top=[k for k in base if k!='tasks' and base[k]!=work[k]]
term=json.loads((D/'task-status.json').read_bytes())['structuredContent'];assert term['taskId']==base['tasks'][839]['taskId']
assert term['status']=='completed' and term['workState']=='result_available' and not term['hasPendingChildRuns'] and not term['hasPendingQuestion'] and term['pendingApproval'] is None
intake=json.loads((D/'intake.json').read_bytes());baseline=json.loads((D/'baseline.json').read_bytes())
assert intake['verdict']=='TECHNICAL' and intake['conditional_on_correctness'] and intake['verification']['status']=='MATCH'
assert snap(R)==json.loads((D/'private/root-before.json').read_bytes())
assert snap(B/'fresh-arithmetic-discovery-r162cb')==json.loads((B/'discovery-arithmetic-r162cb-parent/private/intake/root-before.json').read_bytes())
now=datetime.now(timezone.utc).isoformat()
def update(original):
 x=copy.deepcopy(original);review=x['tasks'][839];review.update(term)
 review.update(observed_utc=now,verdict='TECHNICAL',conditional_on_correctness=True,scope='entire unchanged frozen theorem',contribution_comparison_complete=True,correctness_verdict=None,accepted=False,count_change=0,parent_intake='arithmetic-r162cb-contribution-r1-parent/intake.json',parent_assessment='arithmetic-r162cb-contribution-r1-parent/assessment.md',artifact_status='MATCH',artifact_verification='arithmetic-r162cb-contribution-r1-parent/verification.json',author_files_unchanged=61,status_provenance='Own completed contribution result queried once. Full review,derivation,limits and verifier read. Correctness result not queried; no peer result shared.')
 author=x['tasks'][837];author.update(disposition='CONTRIBUTION_TECHNICAL_CORRECTNESS_PENDING',contribution_gate='TECHNICAL',contribution_conditional_on_correctness=True,contribution_review_task_index=839,correctness_gate=None,accepted=False,count_change=0,author_inputs_unchanged=True)
 key='arithmetic_r162cb_contribution_result';assert key not in x['current_work_snapshot']
 x['current_work_snapshot'][key]=dict(observed_utc=now,task_index=839,verdict='TECHNICAL',conditional_on_correctness=True,entire_unchanged_scope=True,correctness_result_received=False,count_change=0,publication='STOPPED')
 assert [i for i,(a,b) in enumerate(zip(original['tasks'],x['tasks'])) if a!=b]==[837,839]
 assert x['tasks'][838]==original['tasks'][838]
 assert all(x[k]==original[k] for k in original if k not in {'tasks','current_work_snapshot'})
 assert all(x['current_work_snapshot'][k]==v for k,v in original['current_work_snapshot'].items())
 return x
idx=enc(update(base));merged=enc(update(work))
note=('\n\n### R162CB contribution review — '+now+'\n\n'
+'The [independent full contribution review](campaigns/2026-10-14/arithmetic-r162cb-contribution-r1/private/REVIEW.md) classifies the entire unchanged theorem as TECHNICAL,conditional on correctness. Its complete same-configuration reduction pays all simultaneous quotient,cover,part-size and intersection conclusions by source operations and direct incidence/budget calculations. No essential contribution comparison remains open. Correctness remains a separate pending result and was not queried or shared. Parent read the complete review25950bytes,derivation4414bytes,limits10196bytes,handoff and verifier. Reviewer read18canonicaltexts291598bytes and63primarypages:5fullpapers53pages plus10DKMSpages;no visual primary reading,history0,peerinspection0,with original-assignment truncation and ancestry limits disclosed. Read-only artifact MATCH57payloads4873841bytes59files15dirs;all61authorfiles unchanged. Campaign19/20,latestR041,zero increment;publication/downstreamSTOPPED.\n').encode();nj=hj+note
for n,s in baseline['protected'].items():assert sha((P/n).read_bytes())==s
(D/'coordination-rebase.json').write_bytes(enc(dict(intake_head=baseline['head'],integration_head=h,changed_old_tasks=[837,839],pending_correctness_task_untouched=838,foreign_uncommitted_task_indices=foreign,foreign_uncommitted_top_fields=foreign_top,foreign_edits_preserved_and_excluded=True,index_tasks_after_sha256=sha(idx),working_tasks_after_sha256=sha(merged),count_change=0)))
names=['baseline.json','prospective-isolation.json','task-status.json','verify-intake.py','verification.json','assessment.md','intake.json','manage-intake.py','coordination-rebase.json']
paths=[(D/n).relative_to(P).as_posix() for n in names]+[TP,JP];assert len(paths)==len(set(paths))==11
assert git('rev-parse','HEAD').decode().strip()==h and (P/TP).read_bytes()==wt and (P/JP).read_bytes()==wj and not git('diff','--cached','--name-only').strip()
(P/TP).write_bytes(merged);(P/JP).write_bytes(nj)
subprocess.run(['git','add','--',*[n for n in paths if n!=TP]],cwd=P,check=True)
blob=git('hash-object','-w','--stdin',input=idx).decode().strip();subprocess.run(['git','update-index','--add','--cacheinfo','100644',blob,'openai-proof-research/'+TP],cwd=P,check=True)
assert {n for n in git('diff','--cached','--name-only','-z').decode().split('\0') if n}=={'openai-proof-research/'+n for n in paths}
assert git('show',':openai-proof-research/'+TP)==idx
for n in paths:
 if n!=TP:assert git('show',':openai-proof-research/'+n)==(P/n).read_bytes()
subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
assert git('rev-parse','HEAD').decode().strip()==h and (P/TP).read_bytes()==merged and (P/JP).read_bytes()==nj
subprocess.run(['git','commit','-m','Record full-scope technical Ryser contribution review'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip() and git('show','HEAD:openai-proof-research/'+TP)==idx and (P/TP).read_bytes()==merged
assert snap(R)==json.loads((D/'private/root-before.json').read_bytes())
assert snap(B/'fresh-arithmetic-discovery-r162cb')==json.loads((B/'discovery-arithmetic-r162cb-parent/private/intake/root-before.json').read_bytes())
for n,s in baseline['protected'].items():assert sha((P/n).read_bytes())==s
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),changed_old_tasks=[837,839],pending_correctness_untouched=838,staged_paths=11,foreign_edits_preserved=foreign,count=19)))
