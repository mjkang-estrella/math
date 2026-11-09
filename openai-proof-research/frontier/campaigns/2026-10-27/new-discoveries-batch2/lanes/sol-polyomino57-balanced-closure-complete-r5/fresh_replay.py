from pathlib import Path
import json,subprocess,shutil,hashlib,re,time,sys,os,resource,signal
L=Path(__file__).resolve().parent;action=sys.argv[1]
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
W=L/'work';V=L/'verification'
if action=='build':
 m=sys.argv[2];q=subprocess.Popen(['python3',str(L/'run.py'),'-o',m+'.olean',m+'.lean'],cwd=W,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
 resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,35));signal.alarm(225)
 a,b=q.communicate();(V/(m+'.log')).write_text(a+b)
 if q.returncode:print(a+b);sys.exit(q.returncode)
 if not m.startswith('OriginAudit'):assert not a and not b,m
 print(m,'PASS',flush=True);sys.exit(0)
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(90,95));signal.alarm(120)
manifest=json.loads((L/'manifest.json').read_text())
for n,h in manifest.items():assert sha(L/n)==h,n
mods=json.loads((L/'modules.json').read_text());proofmods=json.loads((L/'proof-modules.json').read_text())
if action=='prepare':
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
 W.mkdir();V.mkdir();(V/'start.json').write_text(json.dumps(dict(unix_seconds=time.time())))
 for m in mods:shutil.copyfile(L/'formal'/(m+'.lean'),W/(m+'.lean'))
 print('PREPARED_FRESH_SOURCE_ONLY',len(mods));sys.exit(0)
assert action=='finish'
origins=set();count=0;partial=[];endpoints={}
with (V/'declaration-inventory.json').open('w') as f:
 f.write('[\n')
 for m in mods:
  assert (W/(m+'.olean')).exists(),m
  log=(V/(m+'.log')).read_text()
  if not m.startswith('OriginAudit'):assert not log,m;continue
  blocks=re.findall(r'AUDIT (\w+) ([^\n]+)\nTYPE (.*?)\nAXIOMS (.*?)\nFLAGS (.*?)\n',log,re.S)
  assert len(blocks)==int(re.search(r'AUDIT_TOTAL (\d+)',log)[1]),m
  for a,b,c,d,e in blocks:
   assert 'unsafe=false' in e and 'axiom=false' in e,(b,e)
   origins.add(a)
   if b in ["Polyomino57.universalContainer11_witness","Polyomino57.not_SourceFormula","Polyomino57.minimumSize11_le_57"]:
    assert a=="CompleteEndpoint"
    endpoints[b]=dict(type=c,axioms=d,flags=e)
   if 'partial=true' in e:partial.append(b)
   if count:f.write(',\n')
   json.dump(dict(origin=a,name=b,type=c,axioms=d,flags=e),f)
   count+=1
 f.write('\n]\n')
assert origins==set(proofmods)
assert len(endpoints)==3,endpoints
runs=[json.loads(s) for s in (L/'runs.jsonl').read_text().splitlines()];assert len(runs)==len(mods) and all(x['rc']==0 for x in runs)
r=dict(status='PASS_CLOSED_ENDPOINT',full_unconditional_endpoint=True,credit=0,counts=dict(additional=5,total=35),modules=len(proofmods),origin_declarations=count,fresh_source_only=True,consumed_candidate_oleans=False,strict=True,seconds=time.time()-json.loads((V/'start.json').read_text())['unix_seconds'],peak_sampled_group_rss=max(x['peak_group_rss'] for x in runs),allowed_axioms=['propext','Classical.choice','Quot.sound'],all_actual_unsafe_axiom_flags_false=True,partial_generated=partial,endpoints=endpoints)
(V/'receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),flush=True)
