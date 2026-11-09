import os,resource,subprocess,time,sys,json,pathlib,signal
D=pathlib.Path(__file__).resolve().parents[1]
def pre():
 os.setsid();os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,64*1024**3))
name=sys.argv[1];t=time.monotonic()
env=dict(os.environ,OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1')
root=pathlib.Path('/home/mj-kang/Documents/Dev/math');env['PATH']=str(root/'dlp-research/.tools/lean-4.34.1-linux/bin')+':/usr/bin:/bin';env['LEAN_PATH']=str(D/'proof')+':'+':'.join(str(p) for p in (root/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages').glob('*/.lake/build/lib/lean'))
with (D/'logs'/f'{name}.log').open('w') as f:
 p=subprocess.Popen(sys.argv[2:],cwd=D/'proof',env=env,preexec_fn=pre,stdout=f,stderr=subprocess.STDOUT)
 try: rc=p.wait(timeout=140)
 except subprocess.TimeoutExpired: os.killpg(p.pid,signal.SIGKILL);rc=p.wait()
u=resource.getrusage(resource.RUSAGE_CHILDREN)
r=dict(command=sys.argv[2:],exit=rc,wall=time.monotonic()-t,cpu=u.ru_utime+u.ru_stime,max_rss_kib=u.ru_maxrss,limits='2 CPU affinity, CPU 120 s, wall 140 s, AS 64 GiB; enclosing systemd scope MemoryMax=6G')
(D/'logs'/f'{name}.json').write_text(json.dumps(r,indent=2));print(json.dumps(r));sys.exit(rc)
