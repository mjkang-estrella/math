from pathlib import Path
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
 if m!='ClosureAudit':assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',src.read_text())
 shutil.copyfile(src,W/src.name)
 q=subprocess.run(['python3',str(L/'run.py'),'-o',m+'.olean',m+'.lean'],cwd=W,capture_output=True,text=True)
 (V/(m+'.log')).write_text(q.stdout+q.stderr);print(m,q.returncode,flush=True)
 assert q.returncode==0,m
 if m!='ClosureAudit':assert not q.stdout and not q.stderr,m
text=(V/'ClosureAudit.log').read_text()
n=int(re.search(r'AUDIT_TOTAL (\d+)',text)[1])
blocks=re.findall(r'AUDIT (\w+) ([^\n]+)\nTYPE (.*?)\nAXIOMS (.*?)\nFLAGS (.*?)\n',text,re.S)
assert len(blocks)==n
inventory=[dict(origin=m,name=name,type=t,axioms=a,flags=f) for m,name,t,a,f in blocks]
assert set(x['origin'] for x in inventory)==set(mods)-{'ClosureAudit'}
(V/'declaration-inventory.json').write_text(json.dumps(inventory,indent=2)+'\n')
for name,h in manifest.items():assert sha(L/name)==h
runs=[json.loads(s) for s in (L/'runs.jsonl').read_text().splitlines()]
receipt=dict(status='PASS_COMPONENTS_ONLY',fullSourceClaim=False,credit=0,modules=len(mods),origin_declarations=n,all_dependency_origins_audited=True,allowed_axioms=['propext','Classical.choice','Quot.sound'],partial_generated=[x['name'] for x in inventory if 'partial=true' in x['flags']],fresh_source_only=True,consumed_candidate_oleans=False,seconds=time.monotonic()-t,peak_sampled_group_rss=max(r['peak_group_rss'] for r in runs),strict=True,closure_through=7,row_benchmarks_only=True,missing=['7→8→9→10→11 kernel-certified finite closure','normalized terminal-family to supplied forest correspondence','unconditional UniversalContainer 11 witness','unconditional not SourceFormula'])
(V/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
