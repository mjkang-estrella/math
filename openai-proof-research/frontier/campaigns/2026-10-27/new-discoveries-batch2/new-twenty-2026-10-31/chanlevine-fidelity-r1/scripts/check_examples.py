import os,sys,subprocess,pathlib,json,time
l=pathlib.Path(__file__).resolve().parent.parent
b=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
p=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
e=dict(os.environ,PATH=str(b)+':'+os.environ['PATH'],LEAN_PATH=':'.join([str(l/'build/build')]+[str(x) for x in sorted(p.glob('*/.lake/build/lib/lean'))]),TMPDIR=str(l/'tmp'),XDG_CACHE_HOME=str(l/'cache'),MALLOC_ARENA_MAX='2',PYTHONDONTWRITEBYTECODE='1')
for name,args in [('examples',[b/'lean','-j1','-M3500','-DwarningAsError=true','-o',l/'build/build/FidelityExamples.olean',l/'build/formal/FidelityExamples.lean']),('checker-examples',[b/'leanchecker','FidelityExamples']),('simulation',[sys.executable,'-I',l/'scripts/sanity.py'])]:
 with (l/'logs'/f'{name}-{time.time_ns()}.log').open('w') as f:
  r=subprocess.run([sys.executable,'-I',str(l/'build/scripts/cap.py')]+list(map(str,args)),cwd=(l/'scripts' if name=='simulation' else l/'build/formal'),env=e,stdout=f,stderr=subprocess.STDOUT)
 print(name,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
