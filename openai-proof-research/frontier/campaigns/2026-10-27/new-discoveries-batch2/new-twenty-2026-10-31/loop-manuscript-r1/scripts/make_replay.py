from pathlib import Path
import hashlib,json
D=Path.cwd()
s=(D.parent/'rigid-cube-manuscript-r1/scripts/replay.py').read_text()
s=s[:s.index('try:\n version')]
s=s.replace("D/'receipts'","D/'replay-receipts'").replace("'mathdb364205-'","'mathdb380362-'")
s=s.replace("L.mkdir(exist_ok=True)","assert not L.exists(), 'Use a fresh extraction'; L.mkdir()")
s=s.replace("probe=subprocess.run(['systemd-run'","probe=subprocess.run(['systemd-run'")
s=s.replace("],capture_output=True)\n scope", "],capture_output=True,timeout=10)\n scope")
s=s.replace("wall_seconds=time.monotonic()-t,total_VmRSS_peak", "wall_seconds=time.monotonic()-t,cpu_limit_seconds=120,wall_limit_seconds=140,AS_limit_bytes=64*1024**3,private_RSS_limit_bytes=6*1024**3,cpus=sorted(os.sched_getaffinity(0))[:2],sample_seconds=0.1,total_VmRSS_peak")
s += '''
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
try:
 pins=json.loads((D/'pins.json').read_text())
 for n,h in pins['binaries'].items():assert sha(B/n)==h,'binary hash '+n
 for n,h in json.loads((D/'source-manifest.json').read_text()).items():assert sha(D/n)==h,'source hash '+n
 version=run('version',[str(B/'lean'),'--version'])
 assert pins['lean_commit'] in version and '4.34.1' in version
 for n in ['Loop','ReviewAudit','AllAudit']:
  src=F/(n+'.lean');assert src.exists()
  if n=='Loop':assert not re.search(r'\\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\\b',src.read_text())
  made.extend(F/(n+s) for s in ['.olean','.ilean','.olean.private','.olean.server'])
  run('build-'+n,[str(B/'lean'),'-j1','-DwarningAsError=true','-o',n+'.olean',n+'.lean'])
  run('kernel-'+n,[str(B/'leanchecker'),n])
 a=(L/'build-AllAudit.log').read_text()
 assert 'TOTAL Loop 28' in a and 'unpointed_inequivalence' in a
 controls={
 'NegativeDistance':('import Loop\\nopen Loop380362\\nexample : distance = 96 := by decide\\n','false'),
 'NegativeAssociator':('import Loop\\nopen Loop380362\\nexample : IsAssociator loop assocGroup := by unfold IsAssociator; decide\\n','false'),
 'NegativeEndpoint':('import Loop\\nexample : Loop380362.SourceClaim := Loop380362.source_refutation\\n','type mismatch'),
 'NegativeSorry':('import Loop\\nexample : False := by sorry\\n','sorry'),
 'NegativeAxiom':('import Lean\\naxiom cheat : False\\ntheorem bad : False := cheat\\nopen Lean Elab Command in\\nrun_cmd do\\n let axs ← Lean.collectAxioms `bad\\n for ax in axs do\\n  unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do\\n   throwError "forbidden axiom {ax}"\\n','forbidden axiom cheat')}
 for n,(src,needle) in controls.items():
  p=F/(n+'.lean');assert not p.exists();p.write_text(src);made.append(p)
  out=run(n,[str(B/'lean'),'-j1','-DwarningAsError=true',p.name],False)
  assert needle in out,(n,out)
 (L/'replay.json').write_text(json.dumps(dict(status='PASS',mathdb_id=380362,strict_j1_warningAsError=True,leanchecker_modules=['Loop','ReviewAudit','AllAudit'],full_audit='Loop and reviewer supplement, every attributed declaration',allowed_axioms=['propext','Classical.choice','Quot.sound'],negative_controls=list(controls),runs=receipts,trust='Pinned prebuilt external oleans trusted; no upstream rebuild or source-to-olean attestation.',accepted_credit=0),indent=2)+'\\n')
 print('REPLAY PASS',flush=True)
finally:
 for p in made:
  if p.exists():p.unlink()
'''
(D/'scripts/replay.py').write_text(s)
B=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
pins={'lean_version':'4.34.1','lean_commit':'5045d0056413266e57c625dcd7c365b10e377c52','mathlib_commit':'d13f23b723b8a846827a245b89c10fc7d3f11612','binaries':{n:hashlib.sha256((B/n).read_bytes()).hexdigest() for n in ['lean','leanchecker']},'Loop_sha256':hashlib.sha256((D/'formal/Loop.lean').read_bytes()).hexdigest()}
(D/'pins.json').write_text(json.dumps(pins,indent=2)+'\n')
