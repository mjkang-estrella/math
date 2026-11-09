#!/usr/bin/env python3
"""Source-only strict replay. Run with python3 -I; creates files only under this directory."""
import os,sys,re,subprocess,json,hashlib
from pathlib import Path
root=Path(__file__).resolve().parent
if list(root.rglob('*.olean')):raise SystemExit('Refusing existing oleans; extract a fresh source-only packet.')
manifest=json.loads((root/'source-manifest.json').read_text())
for name,digest in manifest.items():
 if hashlib.sha256((root/name).read_bytes()).hexdigest()!=digest:raise SystemExit('Source hash mismatch: '+name)
lean=Path(os.environ['LEAN_BIN']).resolve();pk=Path(os.environ['LEAN_PACKAGES']).resolve()
for name in ['logs','tmp','home']:(root/name).mkdir(exist_ok=True)
env={'PATH':str(lean.parent)+':/usr/bin:/bin','HOME':str(root/'home'),'TMPDIR':str(root/'tmp'),'MALLOC_ARENA_MAX':'2','PYTHONDONTWRITEBYTECODE':'1','LEAN_PATH':':'.join([str(root/'formal')]+[str(x/'.lake/build/lib/lean') for x in pk.iterdir()])}
os.environ.clear();os.environ.update(env)
if list((root/'logs').glob('*.log')):raise SystemExit('Refusing to overwrite existing logs; extract a fresh packet.')
receipts=[]
def run(label,args,expected=0):
 r=subprocess.run(['/usr/bin/python3','-I',str(root/'scripts/run_capped.py'),str(root/'logs'/label)]+list(map(str,args)),cwd=root,env=env)
 rec=json.loads((root/'logs'/(label+'.json')).read_text());receipts.append(rec)
 if (expected==0 and r.returncode!=0) or (expected!=0 and (r.returncode==0 or rec['cap_reason'])):raise SystemExit('Unexpected result: '+label)
for mod in json.loads((root/'modules.json').read_text()):
 src=root/'formal'/(mod+'.lean')
 if re.search(r'\b(sorry|admit|native_decide|ofReduceBool)\b',src.read_text()):raise SystemExit('Forbidden token')
 run('strict-'+mod+'.log',[lean,'-j1','-DwarningAsError=true','-o',root/'formal'/(mod+'.olean'),src])
 run('leanchecker-'+mod+'.log',[lean.parent/'leanchecker',mod])
controls={
 'WrongDet':(root/'formal/DetPilot.lean').read_text().replace('= 48 :=','= 49 :='),
 'MissingEndpoint':'import Nut\nexample : Nut8.Target := by\n  exact Nut8.nut_sign_character\n',
 'WrongSign':'import Nut\nexample : (-1 : ℝ) = 1 := by\n  norm_num\n',
 'WrongGraphIso':'import GraphChecker\nexample : Nut8.graphIsoCheck 2 6 0 [0, 1] = true := by\n  decide +kernel\n',
 'WrongSwitch':'import Invariances\nexample : Nut8.switch (fun _ : Fin 1 => (2 : ℤ)) !![(1 : ℤ)] = !![(1 : ℤ)] := by\n  decide +kernel\n'}
controls['WrongCheckedLookup'] = 'import CheckedGraphIso\nexample : (Nut8.checkedEquiv (n := 2) [0, 1] (by decide) ⟨0, by omega⟩).val = 1 := by\n  simp [Nut8.checkedEquiv, Nut8.checkedVertex, Equiv.ofBijective]\n'
controls['WrongMask'] = 'import TransportedNeighbors\nexample : (Nut8.transportedMask (⊥ : SimpleGraph (Fin 2)) 0 (Equiv.refl _)).testBit 0 = true := by\n  rw [Nut8.transportedMask_bit]\n  simp\n'
controls['WrongEncoding'] = 'import ExtensionEncoding\nexample : Nut8.graphBit 2 (Nut8.extendGraph 1 0 1) 0 0 = true := by\n  decide +kernel\n'
controls['MissingCoverage'] = 'import FiniteOfParts\nexample : Nut8.Coverage8 := by\n  exact Nut8.coverage8\n'
controls['MissingFiniteObstruction'] = 'import EndpointOfParts\nexample : Nut8.FiniteObstruction := by\n  exact Nut8.finite_obstruction\n'
controls['FourNeighbors'] = 'import Coverage8\nexample : Nut8.eligibleNeighbors 4 0 15 = true := by\n  decide +kernel\n'
controls['FullOldDegree'] = 'import Coverage8\nexample : Nut8.eligibleNeighbors 4 31710 1 = true := by\n  decide +kernel\n'
controls['MissingPerSupport'] = 'import FinalEndpoint\nexample : Nut8.Target := by\n  exact Nut8.nut8_target\n'
for name,source in controls.items():
 f=root/'tmp'/(name+'.lean');f.write_text(source)
 run('negative-'+name+'.log',[lean,'-j1','-DwarningAsError=true',f],expected=1)
(root/'logs/replay.json').write_text(json.dumps({'status':'PASS Coverage8 AND CONDITIONAL ENDPOINT r6p','receipts':receipts},indent=2)+'\n')
print('PASS: r6p Coverage8 and conditional endpoint packet strict rebuild, leanchecker, full audit and rejected negative controls.')
