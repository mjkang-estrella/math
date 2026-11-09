import pathlib,json,hashlib,subprocess,sys,time,resource,datetime
L=pathlib.Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def bindings():
 bs=json.loads((L/'bindings.json').read_text())
 for b in bs:
  assert sha(pathlib.Path(b['original']))==b['sha256'],b['original']
  if 'copy'in b:assert sha(pathlib.Path(b['copy']))==b['sha256']
 return len(bs)
before=bindings();checks=[]
for script,args in [('transfer.py',[]),('compose.py',[]),('close_graph.py',[]),('reconstruct.py',[]),('verify_math.py',[]),('verify_exhaustive.py',[]),('close_graph.py',['0']),('verify_zero.py',[])]:
 start=time.monotonic();p=subprocess.run([sys.executable,str(L/script),*args],capture_output=True,text=True,timeout=190)
 checks.append({'script':script,'args':args,'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'wall_seconds':time.monotonic()-start})
 assert p.returncode==0,checks[-1]
after=bindings()
(L/'capped-checks.json').write_text(json.dumps({'utc':str(datetime.datetime.now(datetime.timezone.utc)),'envelope':{'AS_bytes':536870912,'group_RSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230,'cap_raises':False,'runner':'all subprocesses under assigned helper_guard.py; env threads1/bytecode disabled'},'bindings_before':before,'bindings_after':after,'checks':checks,'child_user_system_seconds':resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime+resource.getrusage(resource.RUSAGE_CHILDREN).ru_stime},indent=2))
sources=[]
for sub in ['scout','current']:
 for p in sorted((L/sub).iterdir()):
  if p.is_file():sources.append({'path':str(p.relative_to(L)),'bytes':p.stat().st_size,'sha256':sha(p)})
(L/'actual-source-bytes.json').write_text(json.dumps({'downloaded':sources,'reused_originals':'bindings.json records scientific source PDFs and extracted texts at immutable r253 paths; no recursive duplication','verification':'all bound originals/copies verified before and after final scientific suite'},indent=2))
(L/'provenance.json').write_text(json.dumps({'lane':str(L),'utc':str(datetime.datetime.now(datetime.timezone.utc)),'counts':{'additional':9,'total':39,'next':40},'status':'RETIRE public exact prior; computational reproduction only','question':'Mattiolo–Mazzuoccolo–Mkrtchyan2104.09241v1 §3Q1','decisive_prior':'Goedgebeur et al2608.10028v4 §5.3Q13 and following paragraph,30Sep2026','source_dependency':'Putman2608.10012v1 Thm1.1; exact reference edge hash matched','local_certificate':'small exact multipole tables; independent no-defect-pruning base enumeration and different-order zero composer','DRAT_replay':False,'scientific_bytes':'actual-source-bytes.json and bindings.json','current_retrieval':'current-access.json, prior-screen.json, prior-precise.json, followup-receipt.json, scout-receipts.json','limits':'bounded queries; no full registry clearance; no denied routes retried; no earliest-version Question13 chronology claim','no_children':True,'no_shared_writes':True},indent=2))
exclude={'final-manifest.json','final-verification.json'}
entries=[{'path':str(p.relative_to(L)),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in exclude]
(L/'final-manifest.json').write_text(json.dumps({'excludes':sorted(exclude),'files':entries},indent=2))
print({'checks':len(checks),'bindings':after,'manifest_files':len(entries),'status':'RETIRE'})
