#!/usr/bin/env python3
"""Fresh, direct CLI invocations of both arithmetic checkers. No checker imports."""
import sys
sys.dont_write_bytecode=True
import argparse,collections,concurrent.futures,hashlib,json,pathlib,subprocess,time
H=pathlib.Path(__file__).resolve().parent;R=H.parents[2]
CHECKERS={'M':R/'verification/highdim/sym5/check_sym5.py','F5':R/'verification/indep5/check_sym_F5.py'}
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(pathlib.Path(p).read_text())
def save(p,v):
 t=p.with_suffix(p.suffix+'.tmp');t.write_text(json.dumps(v,indent=1)+'\n');t.replace(p)
def one(arg):
 f,who,seconds,memory=arg;p=pathlib.Path(f);checker=CHECKERS[who]
 h=sha(p);ch=sha(checker);start=time.monotonic()
 cmd=['bash','-c','ulimit -v '+str(memory)+'; python3 -I -B "$@"','sym7b-direct',str(checker),f,'11']
 if who=='F5':cmd.append('--json')
 r={'file':f,'checker':who,'sha256':h,'checker_sha256':ch,'command':cmd}
 try:
  proc=subprocess.run(cmd,text=True,capture_output=True,timeout=seconds)
  r.update(returncode=proc.returncode,stdout=proc.stdout,stderr=proc.stderr)
  out=json.loads(proc.stdout.strip().splitlines()[-1]);r['check']=out
  assert h==sha(p) and ch==sha(checker),'input changed'
  r['result']='PASS' if proc.returncode==0 and out.get('result')=='PASS' else 'REJECTED_OR_RESOURCE'
 except subprocess.TimeoutExpired as e:r.update(result='TIMEOUT',reason=str(e))
 except Exception as e:r.update(result='ERROR',reason=repr(e))
 r['seconds']=round(time.monotonic()-start,3);return r
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--workers',type=int,default=6);ap.add_argument('--seconds',type=int,default=180);ap.add_argument('--memory',type=int,default=8000000);ap.add_argument('--retry',action='store_true');ap.add_argument('--only-file',default='');ap.add_argument('--exclude-file',default='');ap.add_argument('--only-checker',choices=('M','F5'));ap.add_argument('--ledger',default='checks.json');ap.add_argument('--from-stage',default='');ap.add_argument('--exclude-stage',default='');a=ap.parse_args()
 path=H/a.ledger;old=load(path) if path.exists() else {};queue=[]
 selected=None
 if a.from_stage:
  stages=set(a.from_stage.split(','));selected={r['file'] for s in load(H/'tree.json')['states'].values() for r in s.get('attempts',[]) if r.get('stage') in stages and r['result']=='CERTIFICATE'}
 excluded=set()
 if a.exclude_stage:
  stages=set(a.exclude_stage.split(','));excluded={r['file'] for s in load(H/'tree.json')['states'].values() for r in s.get('attempts',[]) if r.get('stage') in stages and r['result']=='CERTIFICATE'}
 for f in sorted((H/'certs').glob('*.jsonl')):
  if str(f) in excluded:continue
  if selected is not None and str(f) not in selected:continue
  if a.only_file and not any(pattern in f.name for pattern in a.only_file.split(',')):continue
  if a.exclude_file and any(pattern in f.name for pattern in a.exclude_file.split(',')):continue
  for who,checker in CHECKERS.items():
   if a.only_checker and a.only_checker!=who:continue
   r=old.get(str(f),{}).get(who,{})
   if r.get('result')=='PASS' and r.get('sha256')==sha(f) and r.get('checker_sha256')==sha(checker):continue
   if r and not a.retry:continue
   queue.append((str(f),who,a.seconds,a.memory))
 print('queued direct checks',len(queue),flush=True)
 with concurrent.futures.ProcessPoolExecutor(max_workers=a.workers) as pool:
  futures=[pool.submit(one,arg) for arg in queue]
  for n,future in enumerate(concurrent.futures.as_completed(futures),1):
   r=future.result()
   old.setdefault(r['file'],{})[r['checker']]=r;save(path,old)
   with path.with_name(path.stem+'_journal.jsonl').open('a') as out:out.write(json.dumps(r)+'\n')
   print(n,'/',len(queue),r['checker'],pathlib.Path(r['file']).name,r['result'],r['seconds'],flush=True)
 print({who:dict(collections.Counter(v[who]['result'] for v in old.values() if who in v)) for who in CHECKERS},flush=True)
