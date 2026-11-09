#!/usr/bin/env python3
"""Run from a fresh source-only packet directory. No network and no dependency writes."""
from pathlib import Path
import os,sys,subprocess,json,hashlib
D=Path(__file__).resolve().parent
os.chdir(D)
if list(D.rglob('*.olean')):sys.exit('Refusing existing oleans; extract a fresh source-only packet.')
lean=Path(os.environ['LEAN_BIN']).resolve()
packages=Path(os.environ['LEAN_PACKAGES']).resolve()
paths=[str(p/'.lake/build/lib/lean') for p in packages.iterdir() if (p/'.lake/build/lib/lean').is_dir()]
if not paths:sys.exit('No package cache found')
env={'PATH':str(lean.parent)+':/usr/bin:/bin','LEAN_PATH':str(D/'formal')+':'+':'.join(paths),
     'LANG':'C.UTF-8','LC_ALL':'C.UTF-8','MALLOC_ARENA_MAX':'2','TMPDIR':str(D/'tmp')}
(D/'tmp').mkdir();(D/'logs').mkdir(exist_ok=True)
version=subprocess.run([str(lean),'--version'],env=env,capture_output=True,text=True,check=True).stdout.strip()
if '4.34.1' not in version or '5045d0056413266e57c625dcd7c365b10e377c52' not in version:sys.exit('Wrong pinned Lean: '+version)
manifest=json.loads((D/'manifest.json').read_text())
for name,expected in manifest.items():
 if hashlib.sha256((D/name).read_bytes()).hexdigest()!=expected:sys.exit('Source hash mismatch: '+name)
def run(key,args,expected=0):
 cmd=[sys.executable,'-I',str(D/'scripts/guard.py'),str(D/'logs'/key)]+args
 p=subprocess.run(cmd,env=env)
 if (p.returncode==0)!=(expected==0):sys.exit('Unexpected result: '+key)
for mod in ['Foundation','WheelWeights']:
 run(mod+'.log',[str(lean),'-j1','-DwarningAsError=true','-o',str(D/'formal'/(mod+'.olean')),str(D/'formal'/(mod+'.lean'))])
run('audit.log',[str(lean),'-j1','-DwarningAsError=true',str(D/'formal/Audit.lean')])
for mod in ['Foundation','WheelWeights']:
 run('leanchecker-'+mod+'.log',[str(lean.parent/'leanchecker'),mod])
# Negative controls are standalone sources that must be rejected by strict Lean.
controls={
 'false': 'import Foundation\nexample : False := by exact True.intro\n',
 'missing-bound': 'import Foundation\nopen WheelFormal\nexample (G : SimpleGraph (Fin 1)) : 2 ≤ fracChromatic G := by\n  apply weighted_lower_inf G (fun _ => 2) (by intro v; norm_num) 1 (by norm_num)\n',
 'wrong-arithmetic': 'import Foundation\nexample : (2:ℝ) ≤ 0 := by norm_num\n'}
for name,source in controls.items():
 p=D/'formal'/('Negative_'+name+'.lean');p.write_text(source)
 run('negative-'+name+'.log',[str(lean),'-j1','-DwarningAsError=true',str(p)],expected=1)
# Verify the dirty extraction refuses a second run.
p=subprocess.run([sys.executable,'-I',str(D/'replay.py')],env=env,capture_output=True,text=True)
(D/'logs/negative-existing-oleans.log').write_text(p.stdout+p.stderr)
if p.returncode==0 or 'Refusing existing oleans' not in p.stderr:sys.exit('Existing-olean control failed')
print(json.dumps({'status':'partial_components_replayed','lean':version,'main_theorem_proved':False,'credit':0}))
