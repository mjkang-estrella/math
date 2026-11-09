#!/usr/bin/env python3
"""Independent strict replay. Run only in a fresh extraction; no shared writes."""
import shutil,os,sys,pathlib,subprocess,resource,time,signal,json,hashlib,re,uuid
D=pathlib.Path(__file__).resolve().parents[1]
B=pathlib.Path(os.environ['LEAN_BIN']); P=pathlib.Path(os.environ['LEAN_PACKAGES'])
F=D/'formal'; L=D/'replay-receipts'; assert not L.exists(), 'Use a fresh extraction'; L.mkdir()
assert not list(D.rglob('*.olean')), 'Refusing existing oleans'
env={**os.environ,'PATH':str(B)+':'+os.environ.get('PATH','/usr/bin:/bin'),'LEAN_PATH':str(F)+':'+':'.join(str(p) for p in sorted(P.glob('*/.lake/build/lib/lean'))),'MALLOC_ARENA_MAX':'2','OMP_NUM_THREADS':'1','OPENBLAS_NUM_THREADS':'1'}
receipts=[]; made=[]
def run(tag,cmd,ok=True):
 def pre():
  os.setsid();os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,64*1024**3))
 # Use a user scope if available; it is supplementary to process-tree sampling.
 unit='mathdb380362-'+uuid.uuid4().hex
 probe=(subprocess.run(['systemd-run','--user','--scope','--quiet','-p','MemoryMax=6G','true'],capture_output=True,timeout=10) if shutil.which('systemd-run') else subprocess.CompletedProcess([],127,b'',b'systemd-run unavailable'))
 scope=probe.returncode==0
 actual=(['systemd-run','--user','--scope','--quiet','--unit='+unit,'-p','MemoryMax=6G'] if scope else [])+cmd
 t=time.monotonic();peak=private=0;reason=None
 with (L/(tag+'.log')).open('w') as log:
  p=subprocess.Popen(actual,cwd=F,env=env,stdout=log,stderr=subprocess.STDOUT,preexec_fn=pre)
  while p.poll() is None:
   total=priv=0
   for q in pathlib.Path('/proc').glob('[0-9]*'):
    try:
     if os.getpgid(int(q.name))!=p.pid:continue
     s=(q/'status').read_text();total+=int(re.search(r'VmRSS:\s+(\d+)',s)[1])*1024
     sm=(q/'smaps_rollup').read_text();priv+=sum(int(v) for v in re.findall(r'^Private_(?:Clean|Dirty|Hugetlb):\s+(\d+)',sm,re.M))*1024
    except (OSError,TypeError,ProcessLookupError):pass
   peak=max(peak,total);private=max(private,priv)
   if priv>6*1024**3 or time.monotonic()-t>140:
    reason='private RSS or wall limit';os.killpg(p.pid,signal.SIGKILL);break
   time.sleep(.1)
  p.wait()
 r=dict(tag=tag,command=cmd,returncode=p.returncode,wall_seconds=time.monotonic()-t,cpu_limit_seconds=120,wall_limit_seconds=140,AS_limit_bytes=64*1024**3,private_RSS_limit_bytes=6*1024**3,cpus=sorted(os.sched_getaffinity(0))[:2],sample_seconds=0.1,total_VmRSS_peak=peak,private_RSS_peak=private,MemoryMax_6G=scope,scope_probe_error=probe.stderr.decode(),cap_reason=reason)
 receipts.append(r);(L/(tag+'.json')).write_text(json.dumps(r,indent=2)+'\n');print(tag,p.returncode,round(r['wall_seconds'],2),flush=True)
 assert reason is None, r
 if ok:assert p.returncode==0,(tag,(L/(tag+'.log')).read_text()[-5000:])
 else:assert p.returncode!=0 and 'error:' in (L/(tag+'.log')).read_text()
 return (L/(tag+'.log')).read_text()

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
try:
 pins=json.loads((D/'pins.json').read_text())
 assert next(p['rev'] for p in json.loads((D/'dependency-lake-manifest.json').read_text())['packages'] if p['name']=='mathlib')==pins['mathlib_commit']
 for n,h in pins['binaries'].items():assert sha(B/n)==h,'binary hash '+n
 for n,h in json.loads((D/'source-manifest.json').read_text()).items():assert sha(D/n)==h,'source hash '+n
 version=run('version',[str(B/'lean'),'--version'])
 assert pins['lean_commit'] in version and '4.34.1' in version
 for n in ['Loop','ReviewAudit','AllAudit']:
  src=F/(n+'.lean');assert src.exists()
  if n=='Loop':assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',src.read_text())
  made.extend(F/(n+s) for s in ['.olean','.ilean','.olean.private','.olean.server'])
  run('build-'+n,[str(B/'lean'),'-j1','-DwarningAsError=true','-o',n+'.olean',n+'.lean'])
  run('kernel-'+n,[str(B/'leanchecker'),n])
 a=(L/'build-AllAudit.log').read_text()
 assert 'TOTAL Loop 28' in a and 'TOTAL ReviewAudit 2' in a and 'unpointed_inequivalence' in a
 controls={
 'NegativeDistance':('import Loop\nopen Loop380362\nexample : distance = 96 := by decide\n','false'),
 'NegativeAssociator':('import Loop\nopen Loop380362\nexample : IsAssociator loop assocGroup := by unfold IsAssociator; decide\n','false'),
 'NegativeEndpoint':('import Loop\nexample : Loop380362.SourceClaim := Loop380362.source_refutation\n','type mismatch'),
 'NegativeSorry':('import Loop\nexample : False := by sorry\n','sorry'),
 'NegativeAxiom':('import Lean\naxiom cheat : False\ntheorem bad : False := cheat\nopen Lean Elab Command in\nrun_cmd do\n let axs ← Lean.collectAxioms `bad\n for ax in axs do\n  unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do\n   throwError "forbidden axiom {ax}"\n','forbidden axiom cheat')}
 for n,(src,needle) in controls.items():
  p=F/(n+'.lean');assert not p.exists();p.write_text(src);made.append(p)
  out=run(n,[str(B/'lean'),'-j1','-DwarningAsError=true',p.name],False)
  assert needle.lower() in out.lower(),(n,out)
 (L/'replay.json').write_text(json.dumps(dict(status='PASS',mathdb_id=380362,strict_j1_warningAsError=True,leanchecker_modules=['Loop','ReviewAudit','AllAudit'],full_audit='Loop and reviewer supplement, every attributed declaration',allowed_axioms=['propext','Classical.choice','Quot.sound'],negative_controls=list(controls),runs=receipts,trust='Pinned prebuilt external oleans trusted; no upstream rebuild or source-to-olean attestation.',accepted_credit=0),indent=2)+'\n')
 print('REPLAY PASS',flush=True)
finally:
 for p in made:
  if p.exists():p.unlink()
