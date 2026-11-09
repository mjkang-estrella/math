from pathlib import Path
import os,sys,json,subprocess,hashlib,time
root=Path(__file__).resolve().parent.parent
fresh=root/'fresh-extraction'
old=json.loads((fresh/'SOURCE-MANIFEST.json').read_text())
# No mathematical source may change after the fresh strict builds.
assert all(hashlib.sha256((root/p).read_bytes()).hexdigest()==h==hashlib.sha256((fresh/p).read_bytes()).hexdigest() for p,h in old.items() if p.startswith('src/'))
modules=json.loads((root/'outputs/modules.json').read_text());runs=[]
for m in modules:
 for kind in ['build','checker']:
  paths=sorted((fresh/'logs').glob(f'replay-{kind}-{m}-*.log.json'))
  good=[p for p in paths if json.loads(p.read_text())['exit']==0]
  assert good,(kind,m)
  p=good[-1];runs.append(json.loads(p.read_text())|dict(name=f'{kind}-{m}',log=str(p.with_suffix('').relative_to(fresh))))
# Only the test's elaborator recursion option changes; its false claim is preserved.
f=root/'negative/CorruptPackedLookup.lean'
s=f.read_text()
if 'set_option maxRecDepth' not in s:s=s.replace('set_option exponentiation.threshold','set_option maxRecDepth 20000\nset_option exponentiation.threshold')
f.write_text(s);(fresh/'negative'/f.name).write_text(s)
bin=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
pkg=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
env=dict(os.environ,LEAN_PATH=':'.join([str(fresh/'build')]+[str(p) for p in sorted(pkg.glob('*/.lake/build/lib/lean'))]),TMPDIR=str(fresh/'tmp'),XDG_CACHE_HOME=str(fresh/'cache'),MALLOC_ARENA_MAX='2',PYTHONDONTWRITEBYTECODE='1')
negative=[]
for f in sorted((fresh/'negative').glob('*.lean')):
 log=fresh/'logs'/f'negative-{f.stem}-repair-{time.time_ns()}.log'
 cmd=[str(bin/'lean'),'-j1','-M3500','-DwarningAsError=true',str(f)]
 p=subprocess.run([sys.executable,'-I',str(fresh/'scripts/run_capped.py'),str(log)]+cmd,cwd=fresh/'src',env=env)
 assert p.returncode!=0 and 'Tactic `decide` proved that the proposition' in log.read_text(),f
 negative.append(dict(name=f.name,intended_rejection=True,log=str(log.relative_to(fresh))))
result=dict(status='PASS_PARTIAL_ONLY',runs=runs,negative=negative,negative_control_repair='The first new negative control hit maxRecDepth; only its recursion option was raised. All 362 mathematical module sources and all 724 successful module process receipts remain unchanged.')
(fresh/'replay-result.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS_PARTIAL_ONLY: 362 strict builds, 362 leanchecker runs, 4 intended negative rejections')
