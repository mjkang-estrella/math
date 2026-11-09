#!/usr/bin/env python3
"""Source-only strict replay. Run with python3 -I; creates files only under this directory."""
import os,sys,re,subprocess,json
from pathlib import Path
root=Path(__file__).resolve().parent
if list(root.rglob('*.olean')):raise SystemExit('Refusing existing oleans; extract a fresh source-only packet.')
lean=Path(os.environ['LEAN_BIN']).resolve();pk=Path(os.environ['LEAN_PACKAGES']).resolve()
for name in ['logs','tmp','home']:(root/name).mkdir(exist_ok=True)
env={'PATH':str(lean.parent)+':/usr/bin:/bin','HOME':str(root/'home'),'TMPDIR':str(root/'tmp'),'MALLOC_ARENA_MAX':'2','PYTHONDONTWRITEBYTECODE':'1','LEAN_PATH':':'.join([str(root/'formal')]+[str(x/'.lake/build/lib/lean') for x in pk.iterdir()])}
os.environ.clear();os.environ.update(env)
receipts=[]
def run(label,args,expected=0):
 r=subprocess.run(['/usr/bin/python3','-I',str(root/'scripts/run_capped.py'),str(root/'logs'/label)]+list(map(str,args)),cwd=root,env=env)
 rec=json.loads((root/'logs'/(label+'.json')).read_text());receipts.append(rec)
 if (expected==0 and r.returncode!=0) or (expected!=0 and (r.returncode==0 or rec['cap_reason'])):raise SystemExit('Unexpected result: '+label)
for mod in ['Nut','CertificateBench','VerifiedDet','GlobalLabel','Character','SignedQuotient','FiniteGrammar','DetPilot','HardDet','HardCofactor','Audit']:
 src=root/'formal'/(mod+'.lean')
 if re.search(r'\b(sorry|admit|native_decide|ofReduceBool)\b',src.read_text()):raise SystemExit('Forbidden token')
 run('strict-'+mod+'.log',[lean,'-j1','-DwarningAsError=true','-o',root/'formal'/(mod+'.olean'),src])
 run('leanchecker-'+mod+'.log',[lean.parent/'leanchecker',mod])
controls={
 'WrongDet':(root/'formal/DetPilot.lean').read_text().replace('= 48 :=','= 49 :='),
 'MissingEndpoint':'import Nut\nexample : Nut8.Target := by\n  exact Nut8.nut_sign_character\n',
 'WrongSign':'import Nut\nexample : (-1 : ℝ) = 1 := by\n  norm_num\n'}
for name,source in controls.items():
 f=root/'tmp'/(name+'.lean');f.write_text(source)
 run('negative-'+name+'.log',[lean,'-j1','-DwarningAsError=true',f],expected=1)
(root/'logs/replay.json').write_text(json.dumps({'status':'PASS PARTIAL PACKET ONLY','receipts':receipts},indent=2)+'\n')
print('PASS: INCOMPLETE r2 packet strict rebuild, leanchecker, full audit and three rejected negative controls.')
