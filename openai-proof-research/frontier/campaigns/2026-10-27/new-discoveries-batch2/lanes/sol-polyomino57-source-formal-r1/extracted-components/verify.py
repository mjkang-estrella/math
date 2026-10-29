from pathlib import Path
import os,sys,json,hashlib,shutil,subprocess,re,time
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((L/'pins.json').read_text())
assert sha(Path(pins['lean_binary']))==pins['lean_sha256']
assert subprocess.check_output([pins['lean_binary'],'--version'],text=True).strip()==pins['lean_version']
# Read repository metadata without running git; no repository mutation.
def revision(repo):
 g=repo/'.git'
 if g.is_file(): g=(repo/g.read_text().strip().removeprefix('gitdir: ')).resolve()
 head=(g/'HEAD').read_text().strip()
 if not head.startswith('ref: '):return head
 ref=head[5:]
 if (g/ref).exists():return (g/ref).read_text().strip()
 for line in (g/'packed-refs').read_text().splitlines():
  if line.endswith(' '+ref):return line.split()[0]
 raise AssertionError(repo)
for v in pins['packages'].values(): assert revision(Path(v['path']))==v['revision']
mods=['Grid','Growth','Normalization','Bounds','Witness','Pilot']
work=L/'replay'
if work.exists():shutil.rmtree(work)
work.mkdir()
logs=L/'verification';logs.mkdir(exist_ok=True)
for m in mods+['OriginAudit']:
 src=L/'formal'/(m+'.lean')
 if m!='OriginAudit':assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',src.read_text())
 shutil.copy2(src,work/src.name)
start=time.monotonic()
for m in mods+['OriginAudit']:
 args=['python3',str(L/'run.py'),'-o',m+'.olean',m+'.lean']
 q=subprocess.run(args,cwd=work,text=True,capture_output=True)
 (logs/(m+'.log')).write_text(q.stdout+q.stderr)
 assert q.returncode==0,(m,q.returncode,q.stdout,q.stderr)
 if m!='OriginAudit':assert not q.stdout and not q.stderr,(m,q.stdout,q.stderr)
audit=(logs/'OriginAudit.log').read_text()
assert 'Forbidden' not in audit
n=int(re.search(r'AUDIT_TOTAL (\d+)',audit)[1])
assert n==233
blocks=re.findall(r'AUDIT (\w+) ([^\n]+)\nTYPE (.*?)\nAXIOMS (.*?)\nFLAGS (.*?)\n',audit,re.S)
assert len(blocks)==n
inventory=[dict(origin=m,name=name,type=t,axioms=a,flags=f) for m,name,t,a,f in blocks]
(logs/'declaration-inventory.json').write_text(json.dumps(inventory,indent=2)+'\n')
reports=json.loads((L/'runs.jsonl').read_text().splitlines()[-1])
receipt=dict(status='PASS_COMPONENTS_ONLY',fullSourceClaim=False,modules=mods,origin_declarations=n,all_origins_audited=True,partial_generated=[x['name'] for x in inventory if 'partial=true' in x['flags']],allowed_axioms=['propext','Classical.choice','Quot.sound'],fresh_source_only=True,consumed_candidate_oleans=False,warningAsError=True,autoImplicit=False,jobs=1,seconds=time.monotonic()-start,pins_sha256=sha(L/'pins.json'),source_hashes={m:sha(work/(m+'.lean')) for m in mods},pilot_placements=64,missing=['executable normalized layer completeness bridge','safe bitboard semantic correspondence','full kernel generation-closure and terminal-coverage certificate','closed UniversalContainer 11 witness theorem','unconditional source refutation'])
(logs/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
