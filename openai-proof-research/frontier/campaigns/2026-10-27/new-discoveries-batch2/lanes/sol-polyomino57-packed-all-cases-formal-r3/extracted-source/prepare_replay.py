from pathlib import Path
import resource,signal,json,re,shutil,hashlib
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(230)
L=Path(__file__).resolve().parent
pins=json.loads((L/'pins.json').read_text())
assert hashlib.sha256(Path(pins['lean_binary']).read_bytes()).hexdigest()==pins['lean_sha256']
assert (L/'lean-version.txt').read_text().strip()==pins['lean_version']
def revision(repo):
 g=repo/'.git'
 if g.is_file():g=(repo/g.read_text().strip().removeprefix('gitdir: ')).resolve()
 head=(g/'HEAD').read_text().strip()
 if not head.startswith('ref: '):return head
 ref=head[5:]
 if (g/ref).exists():return (g/ref).read_text().strip()
 for line in (g/'packed-refs').read_text().splitlines():
  if line.endswith(' '+ref):return line.split()[0]
 raise AssertionError(str(repo))
for pkg in pins['packages'].values():assert revision(Path(pkg['path']))==pkg['revision']
roots=['AllCases'];mods=[];seen=set()
def visit(m):
 if m in seen:return
 seen.add(m)
 p=L/'formal'/(m+'.lean')
 if not p.exists():
  old=L/'frozen/formal'/(m+'.lean')
  if not old.exists():return
  shutil.copy2(old,p)
 s=p.read_text()
 assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',s),m
 for im in re.findall(r'^import (\S+)',s,re.M):visit(im)
 mods.append(m)
for m in roots:visit(m)
for m in mods:
 old=L/'frozen/formal'/(m+'.lean')
 if old.exists():assert old.read_bytes()==(L/'formal'/(m+'.lean')).read_bytes(),m
(L/'consumed-modules.json').write_text(json.dumps(mods,indent=2)+'\n')
template=(L/'frozen/formal/FiniteAudit.lean').read_text();template=re.sub(r'^import .*\n','',template,flags=re.M);template='import AllCases\nimport Lean\n'+template
st=template.index('  let mods := #[');en=template.index('\n  let allowed',st);template=template[:st]+'  let mods := #['+', '.join('`'+m for m in mods)+']'+template[en:]
(L/'formal/FinalAudit.lean').write_text(template)
(L/'fresh-plan.txt').write_text('\n'.join(mods+['FinalAudit'])+'\n')
manifest={str((L/'formal'/(m+'.lean')).relative_to(L)):dict(sha256=hashlib.sha256((L/'formal'/(m+'.lean')).read_bytes()).hexdigest(),bytes=(L/'formal'/(m+'.lean')).stat().st_size) for m in mods+['FinalAudit']}
(L/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
import zipfile
entries=[L/'formal'/(m+'.lean') for m in mods+['FinalAudit']]
entries += [L/x for x in ['pins.json','run.py','fresh-plan.txt','source-manifest.json','consumed-modules.json','SUMMARY.md','INTERFACE.md','provenance.json','measurements.json','selection-provenance.json','lean-version.txt']]
entries += list(L.glob('*.py'))+list(L.glob('*.sh'))+[L/'runs-development.jsonl',L/'inputs/source-only-component.zip']+list((L/'logs').glob('*.log'))
archive=L/'source-only-component.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for f in sorted(set(entries)):
  zi=zipfile.ZipInfo(str(f.relative_to(L)),date_time=(2026,10,29,0,0,0));zi.compress_type=zipfile.ZIP_DEFLATED;zi.external_attr=0o644<<16;z.writestr(zi,f.read_bytes())
work=L/'extracted-source';assert not work.exists()
with zipfile.ZipFile(archive) as z:z.extractall(work)
(work/'fresh-logs').mkdir()
print(json.dumps(dict(modules=len(mods),archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest())))
