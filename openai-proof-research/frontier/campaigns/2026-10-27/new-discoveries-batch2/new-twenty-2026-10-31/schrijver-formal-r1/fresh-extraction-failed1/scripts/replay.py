from pathlib import Path
import os,sys,json,hashlib,subprocess
root=Path(__file__).resolve().parent.parent
bin=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
packages=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
modules=['Definitions','Checkers','Data27','Controls','Audit']
for d in ['build','logs','tmp','cache']:(root/d).mkdir(exist_ok=True)
env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN','LAKE'))}
env.update(LEAN_PATH=':'.join([str(root/'build')]+[str(p) for p in sorted(packages.glob('*/.lake/build/lib/lean'))]),TMPDIR=str(root/'tmp'),XDG_CACHE_HOME=str(root/'cache'),MALLOC_ARENA_MAX='2',PYTHONDONTWRITEBYTECODE='1')
manifest=json.loads((root/'SOURCE-MANIFEST.json').read_text())
for f,h in manifest.items():assert hashlib.sha256((root/f).read_bytes()).hexdigest()==h,f
commands=[]
for m in modules:
 commands += [('build-'+m,[str(bin/'lean'),'-j1','-M3500','-DwarningAsError=true','-o',str(root/'build'/f'{m}.olean'),m+'.lean']),('checker-'+m,[str(bin/'leanchecker'),m])]
results=[]
for name,cmd in commands:
 log=root/'logs'/f'replay-{name}.log'
 receipt=log.with_suffix('.log.json')
 # A resume is valid only with the same full packet hash and previous successful receipt.
 key=hashlib.sha256((root/'SOURCE-MANIFEST.json').read_bytes()).hexdigest()
 done=log.with_suffix('.done.json')
 if '--resume' in sys.argv and done.exists() and json.loads(done.read_text()).get('packet')==key and (root/'build'/f'{name.split("-",1)[1]}.olean').exists():
  results.append(dict(name=name,resumed=True));continue
 r=subprocess.run([sys.executable,'-I',str(root/'scripts/run_capped.py'),str(log)]+cmd,cwd=root/'src',env=env)
 if r.returncode:raise SystemExit(r.returncode)
 done.write_text(json.dumps(dict(packet=key)))
 results.append(json.loads(receipt.read_text())|dict(name=name))
negative=[]
for f in sorted((root/'negative').glob('*.lean')):
 log=root/'logs'/f'negative-{f.stem}.log'
 cmd=[str(bin/'lean'),'-j1','-M3500','-DwarningAsError=true',str(f)]
 r=subprocess.run([sys.executable,'-I',str(root/'scripts/run_capped.py'),str(log)]+cmd,cwd=root/'src',env=env)
 assert r.returncode!=0 and 'Tactic `decide` proved that the proposition' in log.read_text(),f
 negative.append(dict(name=f.name,intended_rejection=True))
(root/'replay-result.json').write_text(json.dumps(dict(status='PASS_PARTIAL_ONLY',runs=results,negative=negative),indent=2)+'\n')
print('PASS_PARTIAL_ONLY')
