import os,sys,subprocess,resource,time,json,signal
from pathlib import Path
W=Path(__file__).resolve().parent; S=W/'src'
B='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin'
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN','LAKE'))}
env.update(LEAN_PATH=':'.join([str(S)]+[str(p/'.lake/build/lib/lean') for p in sorted(P.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]),PATH=B+':/usr/bin:/bin',MALLOC_ARENA_MAX='2',TMPDIR=str(W/'tmp'))
def lim(): os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); os.setsid()
res=[]
def run(name,cmd,expect=0):
    t=time.monotonic();peak=0;killed=None
    with open(W/'logs'/(name+'.log'),'w') as f:
        p=subprocess.Popen(cmd,cwd=S,env=env,stdout=f,stderr=subprocess.STDOUT,preexec_fn=lim)
        while p.poll() is None:
            try:
                rss=sum(int(l.split()[1]) for pid in [p.pid] for l in open(f'/proc/{pid}/status') if l.startswith('VmRSS:'))
            except Exception: rss=0
            peak=max(peak,rss)
            if rss>5*1024*1024 or time.monotonic()-t>140: killed='cap';os.killpg(p.pid,signal.SIGKILL);break
            time.sleep(0.05)
        p.wait()
    r=dict(name=name,rc=p.returncode,secs=round(time.monotonic()-t,1),peakKiB=peak,killed=killed,ok=(p.returncode==expect and not killed));res.append(r);print(json.dumps(r),flush=True)
    if not r['ok']: (W/'result.json').write_text(json.dumps(res,indent=1));sys.exit('FAIL '+name)
assert not list(S.glob('*.olean'))
run('version',[B+'/lean','--version'])
for m in ['CycDefs','CycRot','CycLower','CycUpper','CycMain','AuditFull']:
    run('build-'+m,[B+'/lean','-j1','-DwarningAsError=true','-o',m+'.olean',m+'.lean'])
for m in ['CycDefs','CycRot','CycLower','CycUpper','CycMain','AuditFull']:
    run('check-'+m,[B+'/leanchecker',m])
for m in ['NegWrongFormula','NegB3']:
    run('neg-'+m,[B+'/lean','-j1','-DwarningAsError=true',m+'.lean'],expect=1)
(W/'result.json').write_text(json.dumps(res,indent=1));print('PASS')
