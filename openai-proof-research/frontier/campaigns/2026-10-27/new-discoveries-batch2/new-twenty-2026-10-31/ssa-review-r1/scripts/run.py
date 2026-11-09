import os,sys,resource,pathlib,subprocess,time,signal,json
D=pathlib.Path(__file__).resolve().parents[1]; name=sys.argv[1]
def pre():
 os.setsid();os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,64*1024**3))
env={**os.environ,'MALLOC_ARENA_MAX':'2','OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1','TMPDIR':str(D/'tmp')}
root=pathlib.Path('/home/mj-kang/Documents/Dev/math');pk=root/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'
env['PATH']=str(root/'dlp-research/.tools/lean-4.34.1-linux/bin')+':'+env['PATH']
env['LEAN_PATH']=str(D/'build')+':'+':'.join(str(p) for p in sorted(pk.glob('*/.lake/build/lib/lean')))
t=time.monotonic();peak=0;reason=None
with (D/'logs'/f'{name}.log').open('w') as f:
 p=subprocess.Popen(sys.argv[2:],stdout=f,stderr=subprocess.STDOUT,preexec_fn=pre,env=env,cwd=D/'source-only')
 while p.poll() is None:
  try:
   vals={l.split(':')[0]:int(l.split()[1])*1024 for l in pathlib.Path(f'/proc/{p.pid}/smaps_rollup').read_text().splitlines() if l.startswith(('Private_Clean:','Private_Dirty:','Private_Hugetlb:'))};peak=max(peak,sum(vals.values()))
  except OSError:pass
  if peak>6*1024**3 or time.monotonic()-t>140:
   reason='private RSS / wall cap';os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.05)
 p.wait()
r=dict(command=sys.argv[2:],returncode=p.returncode,wall_seconds=time.monotonic()-t,peak_sampled_private_bytes=peak,cap_reason=reason,date=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),limits='2 CPUs, CPU 120s, wall 140s, private RSS sampled 6 GiB, AS 64 GiB, MALLOC_ARENA_MAX=2')
(D/'receipts'/f'{name}.json').write_text(json.dumps(r,indent=2));print(json.dumps(r))
sys.exit(p.returncode)
