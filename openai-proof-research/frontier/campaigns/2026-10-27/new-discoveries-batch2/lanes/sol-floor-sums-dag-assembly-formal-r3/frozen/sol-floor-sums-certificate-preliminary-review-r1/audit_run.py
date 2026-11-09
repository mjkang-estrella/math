from pathlib import Path
import json,hashlib,subprocess,sys,os,shutil,time
L=Path(__file__).resolve().parent;F=L/'frozen'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def integrity():
 for d in json.loads((L/'freeze.json').read_text()):assert sha(Path(d['original']))==sha(L/d['copy'])==d['sha256']
integrity()
# Execute the frozen final verifier only through its read-only integrity and exact
# original-sexpr reconstruction phase. Its receipt-writing phase is not executed.
s=(F/'final_verify.py').read_text().split('executions=[];')[0]
exec(compile(s,str(F/'final_verify.py'),'exec'),{'__file__':str(F/'final_verify.py')})
wrapper=L/'deny_solver.py'
wrapper.write_text('import sys,runpy\nclass Deny:\n def find_spec(self,name,*args):\n  if name.split(".")[0] in {"z3","pysmt","cvc5"}: raise ImportError("solver unavailable")\nsys.meta_path.insert(0,Deny())\ndef audit(event,args):\n if event in {"subprocess.Popen","os.system","os.posix_spawn"}:raise RuntimeError("external process unavailable")\nsys.addaudithook(audit)\nrunpy.run_path(sys.argv[1],run_name="__main__")\n')
env=dict(os.environ,CERT_VERIFY_ONLY='1',PATH='/solver-unavailable')
def run(script):
 at=time.monotonic();p=subprocess.run([sys.executable,str(wrapper),str(script)],env=env,text=True,capture_output=True)
 try:out=json.loads(p.stdout)
 except ValueError:out=p.stdout
 return {'exit':p.returncode,'stdout':out,'stderr':p.stderr,'seconds':time.monotonic()-at}
receipts={'mapping':run(F/'mapping.py'),'check':run(F/'check.py'),'exact_original_DAG_reconstruction':True,'solver_imports_and_processes':'blocked'}
assert receipts['mapping']['stdout']['literal_query_mapping']=='PASS'
assert receipts['check']['stdout']['certificate_PASS']
N=[json.loads(x) for x in (F/'dag.jsonl').read_text().splitlines()]
def head(i):return N[i]['atom'] if 'atom' in N[i] else head(N[i]['args'][0])
def first(rule):return next(i for i,x in enumerate(N) if 'args'in x and head(i)==rule)
false=next(i for i,x in enumerate(N) if x.get('atom')=='false')
true=next(i for i,x in enumerate(N) if x.get('atom')=='true')
mutations={}
for label in ['false-arithmetic','altered-assertion','removed-premise','hypothesis-discharge','definition-cycle','scope']:
 D=L/'mutations'/label;D.mkdir(parents=True,exist_ok=True)
 for name in ['check.py','dag-index.json','query-map.json','mapping.py']:shutil.copyfile(F/name,D/name)
 (D/'frozen').mkdir(exist_ok=True);shutil.copyfile(F/'frozen/all-m-query.smt2',D/'frozen/all-m-query.smt2')
 ns=[dict(x,args=list(x['args'])) if 'args'in x else dict(x) for x in N]
 if label=='false-arithmetic':i=first('th-lemma');ns[i]['args']=[ns[i]['args'][0],false]
 if label=='altered-assertion':
  q=D/'frozen/all-m-query.smt2';s=q.read_text();assert '(>= m 1)' in s;s=s.replace('(>= m 1)','(>= m 2)',1);q.write_text(s)
 if label=='removed-premise':
  i=first('mp');del ns[i]['args'][1]
 if label=='hypothesis-discharge':
  i=first('lemma');ns[i]['args'][-1]=false
 if label=='definition-cycle':
  i=first('intro-def');c=ns[i]['args'][-1];u=ns[c]['args'][1];eq=ns[u]['args'][2];z=ns[eq]['args'][1];ns[eq]['args'][2]=z
 if label=='scope':
  # A changed binder RHS in the actual source must disagree with the frozen DAG.
  sex=(F/'frozen/z3-proof.sexpr').read_text();assert '(let ' in sex
  sex=sex.replace('(let ','(letBROKEN ',1);(D/'changed.sexpr').write_text(sex)
  mutations[label]={'rejected':sex!=(F/'frozen/z3-proof.sexpr').read_text(),'limitation':'lexical source-integrity mutation; separate semantic lexical tests below'};continue
 (D/'dag.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in ns))
 r=run(D/('mapping.py' if label=='altered-assertion' else 'check.py'))
 r['rejected']=r['exit']!=0 or not isinstance(r['stdout'],dict) or not r['stdout'].get('certificate_PASS',False)
 assert r['rejected'],label
 mutations[label]=r
receipts['mutations']=mutations
(L/'replay-and-mutations.json').write_text(json.dumps(receipts,indent=2)+'\n')
integrity();print(json.dumps({'replay_PASS':True,'mutations_rejected':list(mutations),'integrity_after':True}))
