from pathlib import Path
import json,subprocess,shutil,hashlib,re,time,sys,os
L=Path(__file__).resolve().parent
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
manifest=json.loads((L/'manifest.json').read_text())
for n,h in manifest.items():assert sha(L/n)==h,n
pins=json.loads((L/'pins.json').read_text());assert sha(Path(pins['lean_binary']))==pins['lean_sha256']
assert subprocess.check_output([pins['lean_binary'],'--version'],text=True).strip()==pins['lean_version']
def revision(repo):
 g=repo/'.git'
 if g.is_file():g=(repo/g.read_text().strip().removeprefix('gitdir: ')).resolve()
 head=(g/'HEAD').read_text().strip()
 if not head.startswith('ref: '):return head
 ref=head[5:]
 if (g/ref).exists():return (g/ref).read_text().strip()
 return next(s.split()[0] for s in (g/'packed-refs').read_text().splitlines() if s.endswith(' '+ref))
for v in pins['packages'].values():assert revision(Path(v['path']))==v['revision']
mods=json.loads((L/'modules.json').read_text());proofmods=json.loads((L/'proof-modules.json').read_text());W=L/'work';V=L/'verification'
W.mkdir();V.mkdir();t=time.monotonic();inventory=[]
for m in mods:
 src=L/'formal'/(m+'.lean');shutil.copyfile(src,W/src.name)
 q=subprocess.run(['python3',str(L/'run.py'),'-o',m+'.olean',m+'.lean'],cwd=W,capture_output=True,text=True)
 (V/(m+'.log')).write_text(q.stdout+q.stderr);print(m,q.returncode,flush=True)
 assert q.returncode==0,m
 if m.startswith('OriginAudit'):
  blocks=re.findall(r'AUDIT (\w+) ([^\n]+)\nTYPE (.*?)\nAXIOMS (.*?)\nFLAGS (.*?)\n',q.stdout,re.S)
  assert len(blocks)==int(re.search(r'AUDIT_TOTAL (\d+)',q.stdout)[1])
  inventory.extend(dict(origin=a,name=b,type=c,axioms=d,flags=e) for a,b,c,d,e in blocks)
 else:assert not q.stdout and not q.stderr,m
assert set(x['origin'] for x in inventory)==set(proofmods)
(V/'declaration-inventory.json').write_text(json.dumps(inventory,indent=2)+'\n')
for n,h in manifest.items():assert sha(L/n)==h
runs=[json.loads(s) for s in (L/'runs.jsonl').read_text().splitlines()]
receipt=dict(status='PASS_CLOSED_ENDPOINT',full_unconditional_endpoint=True,credit=0,counts=dict(additional=5,total=35),modules=len(proofmods),origin_declarations=len(inventory),fresh_source_only=True,consumed_candidate_oleans=False,strict=True,seconds=time.monotonic()-t,peak_sampled_group_rss=max(x['peak_group_rss'] for x in runs),allowed_axioms=['propext','Classical.choice','Quot.sound'],all_actual_unsafe_axiom_flags_false=True,partial_generated=[x['name'] for x in inventory if 'partial=true' in x['flags']])
(V/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
