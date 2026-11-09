import hashlib,json,os,subprocess,sys
from pathlib import Path
mods='CMDRRBase CMDRROccurrence CMDRRCells CMDRRTransport CMDRRSourceTransport CMDRRRows CMDRRCounts CMDRRRepeat CMDRRSwap CMDRRNormalize CMDRRCycles CMDRRFourOrbit CMDRROrbitCard CMDRRSingleCounts CMDRRRowDomain CMDRRCanonical CMDRRNormalizationBridge CMDRRDegree CMDRRSpouseCycles CMDRRRowDegree CMDRRIncidence CMDRRZeroA CMDRRAuditR3'.split()
root=Path.cwd(); dest=root/'extracted-r3'; build=dest/'build'; build.mkdir(parents=True,exist_ok=False)
assert not any(build.iterdir())
pins=json.loads(Path('PINS.json').read_text()); env=dict(os.environ); env['LEAN_PATH']=str(build)+':'+':'.join(env['LEAN_PATH'].split(':')[1:])
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
before={m:sha(root/'src'/f'{m}.lean') for m in mods}
for m in mods:
 s=(root/'src'/f'{m}.lean').read_text()
 subprocess.run([sys.executable,'-I','-B','write_lane.py',f'extracted-r3/src/{m}.lean'],input=s,text=True,check=True)
 assert sha(dest/'src'/f'{m}.lean')==before[m]
steps=[]
for phase in ['strict','checker']:
 for m in mods:
  args=([pins['lean_bin'],'-j1','-M3500','-DwarningAsError=true','-o',str(build/f'{m}.olean'),str(dest/'src'/f'{m}.lean')] if phase=='strict' else [pins['leanchecker_bin'],m])
  cp=subprocess.run([sys.executable,'-I','-B','runner.py',f'replay_r3_{phase}_{m}','--']+args,env=env)
  steps.append(dict(phase=phase,module=m,exit=cp.returncode))
  if cp.returncode: raise SystemExit(cp.returncode)
after={m:sha(root/'src'/f'{m}.lean') for m in mods}; copied={m:sha(dest/'src'/f'{m}.lean') for m in mods}; assert before==after==copied
s=json.dumps(dict(scope='PARTIAL_ONLY_NO_NONEXISTENCE_ENDPOINT',empty_build_verified=True,lean_path=env['LEAN_PATH'],source_hashes_after_checkers=after,oleans={m:sha(build/f'{m}.olean') for m in mods},commands=steps),indent=2)
subprocess.run([sys.executable,'-I','-B','write_lane.py','results/PARTIAL-REPLAY-R3.json'],input=s,text=True,check=True)
