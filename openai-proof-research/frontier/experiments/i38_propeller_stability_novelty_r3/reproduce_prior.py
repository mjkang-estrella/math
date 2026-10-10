"""Run unchanged R2, including author's verifier, intercept every prior output write."""
from pathlib import Path
import hashlib,importlib.util,contextlib,io,json,sys
from unittest.mock import patch
R=Path(__file__).resolve().parents[3];E=Path(__file__).resolve().parent;S=R/'frontier/sources/i38_propeller_stability_novelty_r3';P=R/'frontier/experiments/i38_propeller_stability_r2'
def run():
 baseline=json.loads((S/'prior-before.json').read_text())
 def check():
  for row in baseline:assert hashlib.sha256((R/row['path']).read_bytes()).hexdigest()==row['sha256'],row['path']
 check();sys.path.insert(0,str(P));spec=importlib.util.spec_from_file_location('unchanged_i38_r2',P/'verify.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
 cap=[]
 def intercept(path,data,*args,**kwargs):
  assert path.resolve()==(P/'verification.json').resolve(),str(path);cap.append(json.loads(data));return len(data)
 stdout=io.StringIO()
 with patch.object(Path,'write_text',intercept),contextlib.redirect_stdout(stdout):rc=mod.main()
 assert rc==0 and len(cap)==1 and cap[0]['status']=='PASS';check()
 return {'status':'PASS','unchanged_prior_files':len(baseline),'intercepted_r2_output':str((P/'verification.json').relative_to(R)),'r2':cap[0],'stdout':stdout.getvalue(),'immutable_dependency_drift':[]}
if __name__=='__main__':
 out=run();(E/'prior-reproduction.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['r2','stdout']},indent=2))
