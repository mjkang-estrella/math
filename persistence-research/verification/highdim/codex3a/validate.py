"""Direct subprocess executions of both unchanged checkers. No builtins patching."""
import sys
sys.dont_write_bytecode=True
import os,json,time,hashlib,subprocess,concurrent.futures,shlex,fcntl
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
CHECKERS=[HERE/'checkhd.py',ROOT/'verification/v14_checknd_hd.py']
def check(arg):
    cert,checker,seconds=arg
    meta=json.loads(cert.open().readline());dim=meta['dim']
    brute={1:100,2:60,3:30,4:20}.get(dim,12)
    args=[str(checker),str(cert),str(brute)]
    if checker.name=='checkhd.py':args+=['1']
    cmd='ulimit -v 6000000; exec python3 -I -B '+' '.join(shlex.quote(x) for x in args)
    name=str(cert.relative_to(HERE)).replace('/','__')+'.'+checker.stem+'.log'
    log=HERE/'logs/checks'/name;log.parent.mkdir(parents=True,exist_ok=True)
    start=time.monotonic()
    try:
        with log.open('w') as f:
            p=subprocess.run(['bash','-c',cmd],stdout=f,stderr=subprocess.STDOUT,timeout=seconds)
        code=p.returncode
    except subprocess.TimeoutExpired:code='TIMEOUT'
    tail=log.read_text()[-2048:]
    return str(cert.relative_to(HERE)),checker.name,{'status':'PASS' if code==0 and 'RESULT: PASS' in tail else str(code),
        'returncode':code,'seconds':round(time.monotonic()-start,3),'sha256':hashlib.sha256(cert.read_bytes()).hexdigest(),
        'log':str(log.relative_to(HERE)),'command':['bash','-c',cmd],'brute_Lmax':brute}
def main():
    workers=int(sys.argv[1]) if len(sys.argv)>1 else 12
    seconds=int(sys.argv[2]) if len(sys.argv)>2 else 1200
    assert 1<=workers<=12
    fn=HERE/'checker_results.json';res=json.load(open(fn)) if fn.exists() else {}
    jobs=[]
    for cert in sorted((HERE/'certs').rglob('*.jsonl')):
        if len(sys.argv)>4 and sys.argv[4] not in str(cert):continue
        h=hashlib.sha256(cert.read_bytes()).hexdigest();key=str(cert.relative_to(HERE))
        for checker in CHECKERS:
            if len(sys.argv)>3 and sys.argv[3] not in ('','all') and sys.argv[3] not in checker.name:continue
            old=res.get(key,{}).get(checker.name,{})
            if old.get('status')!='PASS' or old.get('sha256')!=h:jobs.append((cert,checker,seconds))
    print('CHECKS',len(jobs),flush=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        for k,c,r in pool.map(check,jobs):
            with (HERE/'checks.lock').open('a') as lock:
                fcntl.flock(lock,fcntl.LOCK_EX)
                res=json.load(open(fn)) if fn.exists() else {}
                res.setdefault(k,{})[c]=r
                tmp=fn.with_suffix('.tmp');tmp.write_text(json.dumps(res,indent=1)+'\n');os.replace(tmp,fn)
            print(k,c,r['status'],r['seconds'],flush=True)
if __name__=='__main__':main()
