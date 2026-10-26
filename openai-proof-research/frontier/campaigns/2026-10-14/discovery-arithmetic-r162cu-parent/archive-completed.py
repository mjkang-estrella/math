from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,subprocess
P=Path(__file__).resolve().parents[4];B=P/'frontier/campaigns/2026-10-14';TP='frontier/campaigns/2026-10-14/tasks.json';JP='frontier/NEW-TEN-2026-10-14.md'
def git(*a,input=None):return subprocess.check_output(['git',*a],cwd=P,input=input)
def enc(x):return (json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode()
def sha(a):return hashlib.sha256(a).hexdigest()
def snap(root):
 out={}
 for p in root.rglob('*'):
  assert not p.is_symlink()
  if p.is_file():
   a=p.read_bytes();out[p.relative_to(root).as_posix()]={'bytes':len(a),'sha256':sha(a),'mode':p.stat().st_mode}
 return out
for tag,index,extra in [('r162cu',860,['archive-completed.py']),('r163-sol',861,['verify-intake.py','intake-baseline.json','intake-prospective-isolation.json'])]:
 D=B/('discovery-arithmetic-'+tag+'-parent');R=B/('fresh-arithmetic-discovery-'+tag)
 assert not git('diff','--cached','--name-only').strip();h=git('rev-parse','HEAD').decode().strip();ht=git('show',h+':openai-proof-research/'+TP);hj=git('show',h+':openai-proof-research/'+JP);wt=(P/TP).read_bytes();wj=(P/JP).read_bytes();base=json.loads(ht);work=json.loads(wt)
 assert len(base['tasks'])==len(work['tasks'])==862 and base['tasks'][index]==work['tasks'][index] and base['newAccepted']==work['newAccepted']==19
 term=json.loads((D/'task-status.json').read_bytes());intake=json.loads((D/'intake.json').read_bytes());v=json.loads((D/'verification.json').read_bytes())
 assert term['taskId']==base['tasks'][index]['taskId'] and term['status']=='completed' and not term['hasPendingChildRuns'] and term['pendingApproval'] is None
 assert intake['disposition']=='PREFREEZE_NO_NOMINEE' and v['status']=='MATCH' and snap(R)==json.loads((D/'private/intake/root-before.json').read_bytes())
 now=datetime.now(timezone.utc).isoformat()
 def update(original):
  x=copy.deepcopy(original);r=x['tasks'][index];r.update(term);r.update(observed_utc=now,disposition='PREFREEZE_NO_NOMINEE',theorem_frozen=False,diagnostic_frozen=False,correctness_gate=None,contribution_gate=None,accepted=False,count_change=0,parent_intake=str((D/'intake.json').relative_to(P)),parent_assessment=str((D/'assessment.md').relative_to(P)),artifact_status='MATCH',artifact_verification=str((D/'verification.json').relative_to(P)),author_inputs_unchanged=True,author_comparisons=intake['closed_author_comparisons'],unproved_directions=intake['unproved_directions'],reading=intake['reading'],all_old_scopes_preserved=True)
  key=tag.replace('-','_')+'_final_disposition';assert key not in x['current_work_snapshot'];x['current_work_snapshot'][key]={'task_index':index,'disposition':'PREFREEZE_NO_NOMINEE','count_change':0,'artifact_status':'MATCH','publication':'STOPPED'}
  assert all(x[k]==original[k] for k in original if k not in {'tasks','current_work_snapshot'});assert [i for i,(a,b) in enumerate(zip(original['tasks'],x['tasks'])) if a!=b]==[index]
  return x
 idx=enc(update(base));merged=enc(update(work));note=('\n\n### '+tag+' archived — '+now+'\n\nPREFREEZE/no nominee. [Parent assessment](campaigns/2026-10-14/'+D.name+'/assessment.md) preserves completed author comparisons and precise limits. Full handoff,comparison,reading record and verifier read;no mathematical grades assigned. Read-only artifact verification MATCH:'+str(v['payloads'])+'payloads,'+str(v['whole_files'])+'files,'+str(v['source_blobs'])+'source blobs,'+str(v['source_trees_independently_verified'])+'Git trees,five original/copy pairs,three wrong-anchor rejections. Author bytes/full modes unchanged. Source/primary compositions do not increment the campaign. All prior scopes unchanged.19/20,latestR041;publication/downstreamSTOPPED.\n').encode();ij=hj+note;mj=wj+note
 foreign=[i for i,(a,b) in enumerate(zip(base['tasks'],work['tasks'])) if a!=b]
 (D/'archive-record.json').write_bytes(enc({'head':h,'own_task':index,'foreign_task_indices_preserved':foreign,'foreign_journal_preserved':wj!=hj,'count_change':0}))
 names=['task-status.json','assessment.md','intake.json','verification.json','archive-record.json']+extra;paths=[str((D/n).relative_to(P)) for n in names]+[TP,JP]
 assert git('rev-parse','HEAD').decode().strip()==h and (P/TP).read_bytes()==wt and (P/JP).read_bytes()==wj
 (P/TP).write_bytes(merged);(P/JP).write_bytes(mj);subprocess.run(['git','add','--',*[n for n in paths if n not in {TP,JP}]],cwd=P,check=True)
 for path,a in [(TP,idx),(JP,ij)]:
  blob=git('hash-object','-w','--stdin',input=a).decode().strip();subprocess.run(['git','update-index','--add','--cacheinfo','100644',blob,'openai-proof-research/'+path],cwd=P,check=True)
 assert set(filter(None,git('diff','--cached','--name-only','-z').decode().split('\0')))=={'openai-proof-research/'+n for n in paths};subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
 assert git('rev-parse','HEAD').decode().strip()==h and (P/TP).read_bytes()==merged and (P/JP).read_bytes()==mj
 subprocess.run(['git','commit','-m','Archive '+tag+' completed comparison without a nominee'],cwd=P,check=True)
 assert not git('diff','--cached','--name-only').strip() and git('show','HEAD:openai-proof-research/'+TP)==idx and git('show','HEAD:openai-proof-research/'+JP)==ij and (P/TP).read_bytes()==merged and (P/JP).read_bytes()==mj
 assert snap(R)==json.loads((D/'private/intake/root-before.json').read_bytes())
 print(tag,json.dumps({'commit':git('rev-parse','HEAD').decode().strip(),'own_task':index,'foreign_edits_preserved':foreign,'count':19}))
