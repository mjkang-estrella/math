from pathlib import Path
import os,sys,subprocess,json
r=Path(__file__).resolve().parent
lean=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
pk=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
for n in ['logs','tmp','home']:(r/n).mkdir(exist_ok=True)
env={'PATH':str(lean.parent)+':/usr/bin:/bin','HOME':str(r/'home'),'TMPDIR':str(r/'tmp'),'MALLOC_ARENA_MAX':'2','PYTHONDONTWRITEBYTECODE':'1','LEAN_PATH':':'.join([str(r/'formal')]+[str(x/'.lake/build/lib/lean') for x in pk.iterdir()])}
seen=set()
def build(m):
 if m in seen:return
 seen.add(m);p=r/'formal'/(m+'.lean')
 if not p.exists():return
 for ln in p.read_text().splitlines():
  if ln.startswith('import '):
   for dep in ln.split()[1:]:build(dep)
 if (r/'formal'/(m+'.olean')).exists() and '--force' not in sys.argv:return
 log=r/'logs'/f'dev-{m}-{len(list((r/"logs").glob("*.json"))):04}.log'
 cmd=[str(lean),'-j1','-DwarningAsError=true','-o',str(r/'formal'/(m+'.olean')),str(p)]
 rc=subprocess.run(['/usr/bin/python3','-I',str(r/'scripts/run_capped.py'),str(log)]+cmd,env=env,cwd=r).returncode
 if rc:print(log.read_text());sys.exit(rc)
for m in sys.argv[1:]:
 if not m.startswith('--'):build(m)
