import os,resource,signal,json,hashlib,zipfile,shutil
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(25,30));signal.alarm(40)
L=Path(__file__).resolve().parent
base=['Grid','Growth','Normalization','Bounds','Witness','Efficient','Coverage','Existence','ListCertificate','Assembly','SortedCertificate','PlacementTree','LocalAssembly']
mods=base+json.loads((L/'generated-modules.json').read_text())
old=(L/'formal/OriginAudit.lean').read_text();s=old[old.index('import Lean'):];a=s.index('let mods := #[');b=s.index(']',a)
s=s[:a]+'let mods := #['+', '.join('`'+x for x in mods)+']'+s[b+1:]
(L/'formal/ClosureAudit.lean').write_text('import SevenCoverage\n'+s)
D=L/'delivery';D.mkdir(exist_ok=True);(D/'formal').mkdir(exist_ok=True)
for m in mods+['ClosureAudit']:shutil.copyfile(L/'formal'/(m+'.lean'),D/'formal'/(m+'.lean'))
for n in ['run.py','pins.json']:shutil.copyfile(L/n,D/n)
(D/'modules.json').write_text(json.dumps(mods+['ClosureAudit'],indent=2)+'\n')
# Replay starts from source only and validates the immutable package revisions.
script='''from pathlib import Path
import json,subprocess,shutil,hashlib,re,time
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((L/'manifest.json').read_text())
for n,h in manifest.items():assert sha(L/n)==h,n
p=json.loads((L/'pins.json').read_text())
assert sha(Path(p['lean_binary']))==p['lean_sha256']
assert subprocess.check_output([p['lean_binary'],'--version'],text=True).strip()==p['lean_version']
def revision(repo):
 g=repo/'.git'
 if g.is_file():g=(repo/g.read_text().strip().removeprefix('gitdir: ')).resolve()
 head=(g/'HEAD').read_text().strip()
 if not head.startswith('ref: '):return head
 ref=head[5:]
 if (g/ref).exists():return (g/ref).read_text().strip()
 for line in (g/'packed-refs').read_text().splitlines():
  if line.endswith(' '+ref):return line.split()[0]
 raise AssertionError(repo)
for v in p['packages'].values():assert revision(Path(v['path']))==v['revision']
mods=json.loads((L/'modules.json').read_text());W=L/'work';W.mkdir();V=L/'verification';V.mkdir()
t=time.monotonic()
for m in mods:
 src=L/'formal'/(m+'.lean')
 if m!='ClosureAudit':assert not re.search(r'\\b(?:sorry|admit|axiom|unsafe|native_decide)\\b',src.read_text())
 shutil.copyfile(src,W/src.name)
 q=subprocess.run(['python3',str(L/'run.py'),'-o',m+'.olean',m+'.lean'],cwd=W,capture_output=True,text=True)
 (V/(m+'.log')).write_text(q.stdout+q.stderr);print(m,q.returncode,flush=True)
 assert q.returncode==0,m
 if m!='ClosureAudit':assert not q.stdout and not q.stderr,m
text=(V/'ClosureAudit.log').read_text()
n=int(re.search(r'AUDIT_TOTAL (\\d+)',text)[1])
blocks=re.findall(r'AUDIT (\\w+) ([^\\n]+)\\nTYPE (.*?)\\nAXIOMS (.*?)\\nFLAGS (.*?)\\n',text,re.S)
assert len(blocks)==n
inventory=[dict(origin=m,name=name,type=t,axioms=a,flags=f) for m,name,t,a,f in blocks]
assert set(x['origin'] for x in inventory)==set(mods)-{'ClosureAudit'}
(V/'declaration-inventory.json').write_text(json.dumps(inventory,indent=2)+'\\n')
for name,h in manifest.items():assert sha(L/name)==h
runs=[json.loads(s) for s in (L/'runs.jsonl').read_text().splitlines()]
receipt=dict(status='PASS_COMPONENTS_ONLY',fullSourceClaim=False,credit=0,modules=len(mods),origin_declarations=n,all_dependency_origins_audited=True,allowed_axioms=['propext','Classical.choice','Quot.sound'],partial_generated=[x['name'] for x in inventory if 'partial=true' in x['flags']],fresh_source_only=True,consumed_candidate_oleans=False,seconds=time.monotonic()-t,peak_sampled_group_rss=max(r['peak_group_rss'] for r in runs),strict=True,closure_through=7,missing=['7→8→9→10→11 kernel-certified finite closure','normalized terminal-family to supplied forest correspondence','unconditional UniversalContainer 11 witness','unconditional not SourceFormula'])
(V/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\\n');print(json.dumps(receipt),flush=True)
'''
(D/'replay.py').write_text(script)
for n in ['generate.py','setup.py','package.py','input-hashes.json','generation.json','immutable-copy-hashes.json','provenance.json','INTERFACES.md','RESOURCE-NOTES.md']:
 shutil.copyfile(L/n,D/n)
shutil.copytree(L/'failures',D/'failures')
manifest={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(D.rglob('*')) if p.is_file()}
(D/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
archive=L/'source-only-closure.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for p in sorted(D.rglob('*')):
  if p.is_file():
   i=zipfile.ZipInfo(str(p.relative_to(D)),(2026,10,29,0,0,0));i.external_attr=0o100644<<16;i.compress_type=zipfile.ZIP_DEFLATED;z.writestr(i,p.read_bytes())
E=L/'fresh-extracted';E.mkdir()
with zipfile.ZipFile(archive) as z:
 assert not any(n.endswith(('.olean','.ilean','.o','.so')) for n in z.namelist());z.extractall(E)
(L/'archive.json').write_text(json.dumps({'sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'files':len(manifest)+1,'deterministic':True,'no_prebuilt':True},indent=2)+'\n')
