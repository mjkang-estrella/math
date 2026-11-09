#!/usr/bin/env python3
"""Portable sequential replay; execute only in a new safe extraction."""
import os,sys,json,hashlib,pathlib,subprocess,resource,signal,time
ROOT=pathlib.Path(__file__).resolve().parent
F=ROOT/'proof'; O=ROOT/'replay-receipts'
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for x in iter(lambda:f.read(1048576),b''):h.update(x)
 return h.hexdigest()
def run(label,cmd,cwd=None,env=None,expected=0):
 O.mkdir(exist_ok=True)
 cpus=sorted(os.sched_getaffinity(0))[:2]
 def setup():
  os.setsid();os.sched_setaffinity(0,cpus)
  resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,64*1024**3))
 probe=subprocess.run(['systemd-run','--user','--scope','-p','MemoryMax=6G','true'],capture_output=True)
 scope=probe.returncode==0
 actual=(['systemd-run','--user','--scope','-p','MemoryMax=6G','--']+cmd) if scope else cmd
 start=time.monotonic();peak=totalpeak=0;reason=None
 with (O/(label+'.log')).open('w') as out:
  p=subprocess.Popen(actual,cwd=cwd or F,env=env or dict(os.environ,MALLOC_ARENA_MAX='2',OMP_NUM_THREADS='2',OPENBLAS_NUM_THREADS='2'),preexec_fn=setup,stdout=out,stderr=subprocess.STDOUT)
  while p.poll() is None:
   private=total=0
   for q in pathlib.Path('/proc').glob('[0-9]*/status'):
    try:
     if os.getpgid(int(q.parent.name))!=p.pid:continue
     d={s.split(':')[0]:int(s.split()[1])*1024 for s in q.read_text().splitlines() if s.startswith(('VmRSS:','RssAnon:','RssShmem:'))}
     private+=d.get('RssAnon',0)+d.get('RssShmem',0);total+=d.get('VmRSS',0)
    except (OSError,ValueError,ProcessLookupError):pass
   peak=max(peak,private);totalpeak=max(totalpeak,total)
   if private>6*1024**3 or time.monotonic()-start>140:
    reason='private-RSS' if private>6*1024**3 else 'wall';os.killpg(p.pid,signal.SIGKILL);break
   time.sleep(.05)
  p.wait()
 r=dict(label=label,command=cmd,actual_command=actual,cpus=cpus,cpu_seconds=120,wall_limit_seconds=140,AS_GiB=64,private_RSS_limit_GiB=6,peak_private_RSS_bytes=peak,peak_total_VmRSS_bytes=totalpeak,systemd_MemoryMax_6G=scope,scope_probe=probe.stderr.decode(),wall_seconds=time.monotonic()-start,exit=p.returncode,expected=expected,kill_reason=reason)
 (O/(label+'.json')).write_text(json.dumps(r,indent=2)+'\n');print(label,p.returncode,round(r['wall_seconds'],2),flush=True)
 assert p.returncode==expected and reason is None,label
 return r
if __name__=='__main__':
 assert not list(ROOT.rglob('*.olean')), 'Refusing existing oleans: extract afresh'
 assert not O.exists(),'Refusing existing receipts: extract afresh'
 for name,h in json.loads((ROOT/'source-manifest.json').read_text()).items():assert digest(ROOT/name)==h,name
 pins=json.loads((ROOT/'pins.json').read_text())
 B=pathlib.Path(os.environ['LEAN_BIN']).resolve();P=pathlib.Path(os.environ['LEAN_PACKAGES']).resolve()
 for n,key in [('lean','lean_binary_sha256'),('leanchecker','leanchecker_binary_sha256')]:assert digest(B/n)==pins[key]
 assert digest(P/'mathlib/.lake/build/lib/lean/Mathlib.olean')==pins['mathlib_root_olean_sha256']
 env=dict(os.environ,PATH=str(B)+':/usr/bin:/bin',LEAN_PATH=':'.join([str(F)]+[str(x/'.lake/build/lib/lean') for x in sorted(P.iterdir()) if x.is_dir()]),LEAN_NUM_THREADS='1',MALLOC_ARENA_MAX='2',OMP_NUM_THREADS='2',OPENBLAS_NUM_THREADS='2')
 modules=['Clow371639.Defs','Clow371639.LexPower','Clow371639.Refutation','Clow371639.Connected','NegativeControls','ReviewerSanity']
 for m in modules:
  f=m.replace('.','/')
  run(m+'-build',[str(B/'lean'),'-j1','-DwarningAsError=true','-o',f+'.olean',f+'.lean'],env=env)
  run(m+'-checker',[str(B/'leanchecker'),m],env=env)
 for n in ['Audit','PrintAxioms']:run(n,[str(B/'lean'),'-j1','-DwarningAsError=true',n+'.lean'],env=env)
 ax=(O/'PrintAxioms.log').read_text()
 for t in ['not_conjecture','not_connectedConjecture']:
  assert "'Clow371639.%s' depends on axioms: [propext, Classical.choice, Quot.sound]"%t in ax,t
 cases={'c5-independent-bound-one':'example : ∀ T : Finset (Fin 5), (∀ a ∈ T, ∀ b ∈ T, a ≠ b → ¬ Clow371639.c5Adj a b) → T.card ≤ 1 := by decide',
  'c5-clique-bound-one':'example : ∀ T : Finset (Fin 5), (∀ a ∈ T, ∀ b ∈ T, a ≠ b → Clow371639.c5Adj a b) → T.card ≤ 1 := by decide',
  'c5-nonedge':'example : Clow371639.c5Adj 0 2 := by decide'}
 for label,body in cases.items():
  f=F/'RejectedMutation.lean';f.write_text('import Clow371639.LexPower\n'+body+'\n')
  run('reject-'+label,[str(B/'lean'),'-j1','-DwarningAsError=true',f.name],env=env,expected=1)
  assert 'Tactic `decide` proved that the proposition' in (O/('reject-'+label+'.log')).read_text()
  f.unlink()
 lines=(O/'Audit.log').read_text().splitlines();a=[]
 for l in lines:
  if l.startswith('{"'):a.append(json.loads(l))
 assert a and all(x['value_present'] and not x['unsafe'] and not x['partial'] and set(x['axioms'])<=set(['propext','Classical.choice','Quot.sound']) for x in a)
 assert any(x['name']=='Clow371639.not_conjecture' for x in a)
 (O/'declarations.json').write_text(json.dumps(a,indent=2)+'\n')
 (O/'result.json').write_text(json.dumps(dict(status='PASS',builds=len(modules),leanchecker=len(modules),declarations=len(a),negative_controls=len(cases),accepted_credit=0),indent=2)+'\n')
