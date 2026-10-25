#!/usr/bin/env python3
"""Record correctness PASS only; preserve unrelated shared-index work."""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,subprocess
P=Path(__file__).resolve().parents[5];D=Path(__file__).resolve().parent;B=D.parent.parent
R=B/'arithmetic-r162bo-proof-r1';AR=B/'fresh-arithmetic-discovery-r162bo'
TP='frontier/campaigns/2026-10-14/tasks.json';JP='frontier/NEW-TEN-2026-10-14.md'
def git(*a,input=None):return subprocess.check_output(['git',*a],cwd=P,input=input)
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
wt=(P/TP).read_bytes();wj=(P/JP).read_bytes();assert hj==wj
base=json.loads(ht);work=json.loads(wt);assert len(base['tasks'])==len(work['tasks'])
for n in [822,823]:assert base['tasks'][n]==work['tasks'][n]
assert work['newAccepted']==base['newAccepted']==19 and work['latestAcceptance']==base['latestAcceptance']=='R041'
assert base['tasks'][823]['clientRequestId']=='twenty-20261025-arithmetic-r162bo-proof-codex-astra-r1'
foreign=[i for i,(a,b) in enumerate(zip(base['tasks'],work['tasks'])) if a!=b]
foreign_top=[k for k in base if k!='tasks' and base[k]!=work[k]]
term=json.loads((D/'task-status.json').read_bytes())['structuredContent']
assert term['status']=='completed' and term['workState']=='result_available' and term['taskId']==base['tasks'][823]['taskId']
assert not term['hasPendingChildRuns'] and not term['hasPendingQuestion'] and term['pendingApproval'] is None
v=json.loads((D/'verification.json').read_bytes());i=json.loads((D/'intake.json').read_bytes());assert v['status']=='MATCH' and i['verdict']=='PASS'
assert snap(R)==json.loads((D/'review-before.json').read_bytes()) and snap(AR)==json.loads((D/'author-before.json').read_bytes())
baseline=json.loads((D/'baseline.json').read_bytes())
for n,x in baseline['protected'].items():assert sha((P/n).read_bytes())==x
now=datetime.now(timezone.utc).isoformat()
def update(obj):
 x=copy.deepcopy(obj);review=x['tasks'][823];review.update(term)
 review.update(observed_utc=now,verdict='PASS',correctness_gate='PASS',entire_unchanged_scope=True,self_contained=True,proof_requires_source_stipulation=False,statement_sha256=v['statement_sha256'],author_proof_sha256=v['proof_sha256'],parent_intake='discovery-arithmetic-r162bo-parent/proof-intake/intake.json',parent_assessment='discovery-arithmetic-r162bo-parent/proof-intake/assessment.md',artifact_status='MATCH',artifact_verification='discovery-arithmetic-r162bo-parent/proof-intake/verification.json',sealed_review_root_unchanged=True,author_inputs_unchanged=True,contribution_gate=None,accepted=False,count_change=0,status_provenance='Own terminal result queried once. Full independent MATHEMATICS,DEPENDENCIES,reading limits,handoffs and verifier read;correctness PASS for the self-contained proof without a source-truth dependency. No contribution query or peer inspection.')
 author=x['tasks'][822];author.update(disposition='AUTHOR_PROOF_CORRECTNESS_PASS_CONTRIBUTION_PENDING',correctness_gate='PASS',correctness_review_intake='discovery-arithmetic-r162bo-parent/proof-intake/intake.json',correctness_review_statement_sha256=v['statement_sha256'],correctness_review_proof_sha256=v['proof_sha256'],contribution_gate=None,accepted=False,count_change=0)
 key='arithmetic_r162bo_correctness_intake';assert key not in x['current_work_snapshot']
 x['current_work_snapshot'][key]=dict(observed_utc=now,task_index=823,verdict='PASS',entire_unchanged_scope=True,self_contained=True,source_stipulation_required=False,contribution_pending=True,count_change=0,newAccepted=19,latestAcceptance='R041',publication='STOPPED')
 assert [j for j,(a,b) in enumerate(zip(obj['tasks'],x['tasks'])) if a!=b]==[822,823]
 assert all(x[k]==obj[k] for k in obj if k not in {'tasks','current_work_snapshot'})
 assert all(x['current_work_snapshot'][k]==a for k,a in obj['current_work_snapshot'].items())
 return x
idx=enc(update(base));merged=enc(update(work))
note=('\n\n### R162BO correctness PASS; contribution pending — '+now+'\n\n'
+'The independent sharp interval-variance-energy correctness review passes the entire unchanged E(rho)<=H(rho)/3 statement,including arbitrary countably supported finite-Shannon-entropy laws without moments and optimality. Parent adopts correctness PASS only. The proof is self-contained in elementary variance algebra,integration,Jensen and local moment/Fatou convergence;Source148 truth is not required. No necessary correction or essential unverified dependency remains. Parent read full MATHEMATICS5141bytes,DEPENDENCIES7482bytes,READING-LIMITS6831bytes and handoffs/verifier. Reviewer fully read9canonicaltexts77648bytes and4complete primary/companion extracts65pages;other bodies/transitive ancestry unread and not essential. Model-generated supplements are non-stipulated comparison material;known sharpness/entropy-loss improvements credited. Manifest-display truncation recovered;zero history/peer consultation. Parent/bundled artifact MATCH19payloads101699bytes21files3directories;all60author files/frozen hashes unchanged. Wronganchorsrejected,restoredfixturepassed;artifact checks do not grade mathematics. Contribution review remains outstanding,no peer polling or inspection. Campaign19/20,latestR041;publication/downstreamSTOPPED. Unrelated uncommitted task-index changes preserved and excluded.\n').encode()
nj=hj+note
(D/'coordination-rebase.json').write_bytes(enc(dict(intake_head=baseline['head'],integration_head=h,changed_old_task_indices=[822,823],foreign_uncommitted_task_indices=foreign,foreign_uncommitted_top_fields=foreign_top,foreign_edits_preserved_and_excluded_from_commit=True,head_tasks_before_sha256=sha(ht),working_tasks_before_sha256=sha(wt),indexed_tasks_after_sha256=sha(idx),working_tasks_after_sha256=sha(merged),journal_prefix_preserved=True,count_change=0)))
names=['baseline.json','task-status.json','verify-intake.py','verification.json','assessment.md','intake.json','manage.py','coordination-rebase.json'];paths=[(D/n).relative_to(P).as_posix() for n in names]+[TP,JP]
assert git('rev-parse','HEAD').decode().strip()==h and (P/TP).read_bytes()==wt and (P/JP).read_bytes()==wj
(P/TP).write_bytes(merged);(P/JP).write_bytes(nj)
subprocess.run(['git','add','--',*[n for n in paths if n!=TP]],cwd=P,check=True)
blob=git('hash-object','-w','--stdin',input=idx).decode().strip();subprocess.run(['git','update-index','--add','--cacheinfo','100644',blob,'openai-proof-research/'+TP],cwd=P,check=True)
assert {n for n in git('diff','--cached','--name-only','-z').decode().split('\0') if n}=={'openai-proof-research/'+n for n in paths}
assert git('show',':openai-proof-research/'+TP)==idx
for n in paths:
 if n!=TP:assert git('show',':openai-proof-research/'+n)==(P/n).read_bytes()
subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
assert git('rev-parse','HEAD').decode().strip()==h and (P/TP).read_bytes()==merged and (P/JP).read_bytes()==nj
subprocess.run(['git','commit','-m','Record sharp variance-energy correctness PASS; contribution pending'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip() and (P/TP).read_bytes()==merged and git('show','HEAD:openai-proof-research/'+TP)==idx
assert snap(R)==json.loads((D/'review-before.json').read_bytes()) and snap(AR)==json.loads((D/'author-before.json').read_bytes())
for n,x in baseline['protected'].items():assert sha((P/n).read_bytes())==x
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),changed_tasks=[822,823],foreign_edits_preserved=foreign,count=19,correctness='PASS',contribution='pending',review_and_author_unchanged=True)))
