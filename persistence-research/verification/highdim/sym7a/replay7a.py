"""Invoke the two ORIGINAL CLI checkers directly, never import either checker."""
import sys
sys.dont_write_bytecode=True
import argparse,collections,concurrent.futures,hashlib,json,pathlib,subprocess,time
H=pathlib.Path(__file__).resolve().parent;R=H.parents[2]
def read(p):return json.loads(pathlib.Path(p).read_text())
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def save(p,o):
 t=p.with_suffix(p.suffix+'.tmp');t.write_text(json.dumps(o,indent=1)+'\n');t.replace(p)
def work(z):
 f,w,timeout,mem=z
 checker=H.parent/'sym5/check_sym5.py' if w=='M' else R/'verification/indep5/check_sym_F5.py'
 cmd=['bash','-c','ulimit -v '+str(mem)+'; python3 -I "$@"','sym7a-direct',str(checker),f,'11']+(['--json'] if w=='F5' else [])
 start=time.monotonic();out={'command':cmd,'sha256':sha(f),'checker_sha256':sha(checker),'brute_Lmax':11,'memory_kib':mem}
 try:
  r=subprocess.run(cmd,capture_output=True,text=True,timeout=timeout)
  try:result=json.loads(r.stdout.strip().splitlines()[-1])
  except (IndexError,json.JSONDecodeError):result={'result':'ERROR','stdout':r.stdout[-2000:],'stderr':r.stderr[-2000:]}
  out.update(result=result['result'],check=result,returncode=r.returncode)
 except subprocess.TimeoutExpired:out['result']='TIMEOUT'
 out['seconds']=round(time.monotonic()-start,3)
 return f,w,out

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--workers',type=int,default=2);ap.add_argument('--timeout',type=int,default=300);ap.add_argument('--memory',type=int,default=8000000);a=ap.parse_args()
 files=set(str(p) for p in (H/'certs').glob('*.jsonl'))
 for p in H.glob('tree_*.json'):files.update(read(p)['used'])
 path=H/'dual_checks.json';records=read(path) if path.exists() else {}
 jobs=[(f,w,a.timeout,a.memory) for f in sorted(files) for w in ('M','F5') if not (records.get(f,{}).get(w,{}).get('result')=='PASS' and records[f][w]['sha256']==sha(f) and records[f][w]['checker_sha256']==sha(H.parent/'sym5/check_sym5.py' if w=='M' else R/'verification/indep5/check_sym_F5.py'))]
 with concurrent.futures.ThreadPoolExecutor(max_workers=a.workers) as ex:
  pending=[ex.submit(work,z) for z in jobs]
  for future in concurrent.futures.as_completed(pending):
   f,w,r=future.result();records.setdefault(f,{})[w]=r
   with (H/'dual_journal.jsonl').open('a') as stream:stream.write(json.dumps({'file':f,'checker':w,**r})+'\n')
   save(path,records);print(w,r['result'],round(r['seconds'],2),pathlib.Path(f).name,flush=True)
 print(json.dumps({w:dict(collections.Counter(v[w]['result'] for v in records.values() if w in v)) for w in ('M','F5')}))
if __name__=='__main__':main()
