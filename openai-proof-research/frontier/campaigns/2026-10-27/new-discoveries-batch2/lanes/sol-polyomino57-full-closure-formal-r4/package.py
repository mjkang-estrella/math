from pathlib import Path
import json,shutil,hashlib,zipfile,resource,signal
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,35));signal.alarm(45)
L=Path(__file__).resolve().parent;D=L/'delivery';(D/'formal').mkdir(parents=True,exist_ok=True)
base=json.loads((L/'closure/modules.json').read_text())[:-1]
mods=base+['FamilyAssembly','FamilyTree','Layer8','Closure7C000','Closure7C047','Closure7C094']+['Local%dN%d'%(n,c) for n in [7,8,9,10] for c in [8,32,128]]
mods+=json.loads((L/'tree/modules.json').read_text())
for m in mods:
 src=next(p for p in [L/'closure/formal'/(m+'.lean'),L/'formal'/(m+'.lean'),L/'bench/formal'/(m+'.lean'),L/'local'/(m+'.lean'),L/'tree'/(m+'.lean')] if p.exists())
 shutil.copyfile(src,D/'formal'/src.name)
s=(L/'closure/formal/ClosureAudit.lean').read_text();s=s[s.index('import Lean'):];a=s.index('let mods := #[');b=s.index(']',a)
s=s[:a]+'let mods := #['+', '.join('`'+m for m in mods)+']'+s[b+1:]
(D/'formal/ClosureAudit.lean').write_text('\n'.join('import '+m for m in mods)+'\n'+s)
for n in ['run.py','pins.json']:shutil.copyfile(L/'closure'/n,D/n)
(D/'modules.json').write_text(json.dumps(mods+['ClosureAudit'],indent=2)+'\n')
s=(L/'closure/replay.py').read_text().replace("closure_through=7,missing=", "closure_through=7,row_benchmarks_only=True,missing=")
(D/'replay.py').write_text(s)
for n in ['enumerate.py','generate_local.py','benchmark_setup.py','generate_large.py','generate_tree.py','benchmark-results.json','input-hashes.json','SUMMARY.md','INTERFACES.md','RESOURCE-NOTES.md','GAPS.json']:
 shutil.copyfile(L/n,D/n)
shutil.copytree(L/'failures',D/'failures',dirs_exist_ok=True)
E=D/'experiments';E.mkdir(exist_ok=True)
for dirname in ['bench','tree','local']:
 out=E/dirname;out.mkdir(exist_ok=True)
 for p in (L/dirname).iterdir():
  if p.is_file() and p.suffix in ['.lean','.log','.json','.jsonl','.py']:shutil.copyfile(p,out/p.name)
manifest={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(D.rglob('*')) if p.is_file() and p.name!='manifest.json'}
(D/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
with zipfile.ZipFile(L/'source-only-r4.zip','w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for p in sorted(D.rglob('*')):
  if p.is_file():
   i=zipfile.ZipInfo(str(p.relative_to(D)),(2026,10,29,0,0,0));i.external_attr=0o100644<<16;i.compress_type=zipfile.ZIP_DEFLATED;z.writestr(i,p.read_bytes())
(L/'archive.json').write_text(json.dumps(dict(sha256=hashlib.sha256((L/'source-only-r4.zip').read_bytes()).hexdigest(),files=len(manifest)+1,no_prebuilt=True),indent=2)+'\n')
