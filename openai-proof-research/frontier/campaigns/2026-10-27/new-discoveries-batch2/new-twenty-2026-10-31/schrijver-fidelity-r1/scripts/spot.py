from pathlib import Path
import os,subprocess,json,sys
l=Path(__file__).resolve().parent.parent;e=l/'extracted'
bin=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
pkg=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
env=dict(os.environ,PATH=str(bin)+':'+os.environ.get('PATH','/usr/bin:/bin'),TMPDIR=str(l/'tmp'),TMP=str(l/'tmp'),TEMP=str(l/'tmp'),XDG_CACHE_HOME=str(l/'cache'),MALLOC_ARENA_MAX='2',PYTHONDONTWRITEBYTECODE='1',LEAN_PATH=':'.join([str(e/'build')]+[str(p) for p in sorted(pkg.glob('*/.lake/build/lib/lean'))]))
mods=['Definitions','Checkers','Encoding','Enumeration','Rotations','IndexedCertificates','MaskSemantics','MetricTransport','PathGenerator','PathCoverage','Enumeration27Proof','Enumeration28Proof','BridgeTransport','RotationCheck','Rotation28_000','RotationCoverage28','LowerIndexed','Tree27_000','Tree28_000','EndpointRound5','ClosureAuditRound5']
results=[]
for m in mods:
 cmd=[str(bin/'lean'),'-j1','-M3500','-DwarningAsError=true','-o',str(e/'build'/f'{m}.olean'),f'{m}.lean']
 r=subprocess.run([sys.executable,'-I',str(l/'scripts/run_capped.py'),str(l/'logs'/f'build-{m}.log')]+cmd,cwd=e/'src',env=env)
 results.append({'module':m,'exit':r.returncode});(l/'spot-results.json').write_text(json.dumps(results,indent=2)+'\n')
 if r.returncode: print('Failed',m,flush=True)
for m in ['EndpointRound5','ClosureAuditRound5']:
 r=subprocess.run([sys.executable,'-I',str(l/'scripts/run_capped.py'),str(l/'logs'/f'checker-{m}.log'),str(bin/'leanchecker'),m],cwd=e/'src',env=env)
 results.append({'checker':m,'exit':r.returncode});(l/'spot-results.json').write_text(json.dumps(results,indent=2)+'\n')
