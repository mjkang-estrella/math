"""Review runner: capped strict lean/leanchecker runs. 2 CPUs, CPU 120s, wall 140s,
AS 12GiB, sampled-RSS guard 6GiB. Full receipts kept per stage."""
import os,resource,subprocess,time,sys,pathlib,json
LANE=pathlib.Path(__file__).resolve().parents[1]
name=sys.argv[1]
def pre():
    os.setsid()
    os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
    resource.setrlimit(resource.RLIMIT_CPU,(120,120))
    resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))
t=time.monotonic(); peak=0; reason=None
logdir=LANE/'audit/pi-r2-logs'; logdir.mkdir(parents=True,exist_ok=True)
with (logdir/f'{name}.log').open('wb') as log:
    env={**os.environ,'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'2','MALLOC_ARENA_MAX':'2'}
    p=subprocess.Popen(sys.argv[2:],stdout=log,stderr=subprocess.STDOUT,preexec_fn=pre,env=env,cwd=str(LNE) if (LNE:=LANE) else '.')
    while p.poll() is None:
        try:
            rss=int(next(l.split()[1] for l in pathlib.Path(f'/proc/{p.pid}/status').read_text().splitlines() if l.startswith('VmRSS:')))*1024
            peak=max(peak,rss)
        except (OSError,StopIteration): pass
        if peak>6*1024**3 or time.monotonic()-t>140:
            reason='RSS or wall cap'; os.killpg(p.pid,15)
            time.sleep(2)
            if p.poll() is None: os.killpg(p.pid,9)
            break
        time.sleep(.05)
    p.wait()
rec={'returncode':p.returncode,'wall_seconds':round(time.monotonic()-t,3),'sampled_process_rss_peak_bytes':peak,'cap_reason':reason,
     'limits':'2 CPUs; CPU 120s; wall 140s; sampled RSS 6GiB; AS 12GiB; sampler observes child leader only'}
(LANE/'audit'/f'{name}.receipt.json').write_text(json.dumps(rec,indent=1)+'\n')
print(json.dumps(rec))
sys.exit(0 if p.returncode==0 else 1)
