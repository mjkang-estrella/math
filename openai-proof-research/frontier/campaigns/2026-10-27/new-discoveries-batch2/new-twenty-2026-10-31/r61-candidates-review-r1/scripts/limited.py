# Run a command under caps: 2 CPUs, CPU 120 s (RLIMIT_CPU), wall 140 s, private RSS (sum of RssAnon over process group) 6 GiB.
import os,resource,subprocess,time,sys,pathlib,json,signal
L=pathlib.Path(__file__).resolve().parents[1]
name=sys.argv[1]
def pre():
    os.setsid(); os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
    resource.setrlimit(resource.RLIMIT_CPU,(120,120))
def anon(pgid):
    tot=0
    for d in pathlib.Path('/proc').iterdir():
        if not d.name.isdigit(): continue
        try:
            if os.getpgid(int(d.name))!=pgid: continue
            for l in (d/'status').read_text().splitlines():
                if l.startswith('RssAnon:'): tot+=int(l.split()[1])*1024
        except (OSError,ProcessLookupError): pass
    return tot
t=time.monotonic(); peak=0; reason=None
with (L/f'logs/{name}.log').open('w') as log:
    p=subprocess.Popen(sys.argv[2:],stdout=log,stderr=subprocess.STDOUT,preexec_fn=pre,env={**os.environ,'OMP_NUM_THREADS':'2','OPENBLAS_NUM_THREADS':'1'})
    while p.poll() is None:
        peak=max(peak,anon(p.pid))
        if peak>6*1024**3: reason='private RSS cap'
        if time.monotonic()-t>140: reason='wall cap'
        if reason:
            os.killpg(p.pid,signal.SIGKILL); break
        time.sleep(.05)
    p.wait()
ru=resource.getrusage(resource.RUSAGE_CHILDREN)
r={'cmd':sys.argv[2:],'returncode':p.returncode,'wall_seconds':round(time.monotonic()-t,3),'cpu_user_sys_seconds':round(ru.ru_utime+ru.ru_stime,3),'peak_private_rss_bytes_sampled':peak,'cap_reason':reason,'limits':'2 CPUs affinity; RLIMIT_CPU 120 s; wall 140 s; sampled RssAnon sum over process group 6 GiB','utc_end':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
(L/f'logs/{name}.receipt.json').write_text(json.dumps(r,indent=2)+'\n'); print(json.dumps(r))
