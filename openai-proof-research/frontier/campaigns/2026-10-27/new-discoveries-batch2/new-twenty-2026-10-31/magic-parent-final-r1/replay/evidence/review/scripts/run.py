import os,resource,subprocess,time,json,sys,pathlib
r=pathlib.Path(__file__).resolve().parents[1]; name=sys.argv[1];cmd=sys.argv[2:]
def pre():
 os.setsid();os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120))
t=time.monotonic()
with (r/'logs'/f'{name}.log').open('w') as f:
 p=subprocess.Popen(["systemd-run","--user","--scope","-p","MemoryMax=6G"]+cmd,stdout=f,stderr=subprocess.STDOUT,preexec_fn=pre)
 try: code=p.wait(timeout=140)
 except subprocess.TimeoutExpired:
  os.killpg(p.pid,9);code=p.wait()
(r/'receipts'/f'{name}.json').write_text(json.dumps(dict(command=cmd,exit=code,wall=time.monotonic()-t,limits='2 CPUs; CPU 120s; wall 140s; systemd MemoryMax=6G'),indent=2));print(name,code);sys.exit(code)
