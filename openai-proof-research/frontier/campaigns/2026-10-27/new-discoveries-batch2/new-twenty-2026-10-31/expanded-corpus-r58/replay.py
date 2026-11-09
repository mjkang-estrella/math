from pathlib import Path
import subprocess,os,hashlib,json,shutil,re,sys
O=Path(__file__).resolve().parent; ROOT=Path('/home/mj-kang/Documents/Dev/math'); fresh=O/'extracted-strict'; fresh.mkdir(exist_ok=True); names=['Defs','BoolProbe','Checker','Endpoint','Audit']; rows=[]
for n in names:
 data=(O/(n+'.lean')).read_bytes()
 if re.search(rb'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',data) and n!='Audit':raise RuntimeError('forbidden source token '+n)
 if not b'set_option warningAsError true' in data:raise RuntimeError('strict option missing')
 (fresh/(n+'.lean')).write_bytes(data)
for p in fresh.glob('*.olean'):p.unlink()
PACK=ROOT/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages';env=os.environ.copy();env['LEAN_PATH']=':'.join([str(fresh)]+[str(p/'.lake/build/lib/lean') for p in PACK.iterdir()]);env['LEAN_NUM_THREADS']='1'
for n in names:
 cmd=[str(ROOT/'dlp-research/.tools/lean-4.34.1-linux/bin/lean'),'-j1','-DwarningAsError=true','-o',str(fresh/(n+'.olean')),str(fresh/(n+'.lean'))]
 r=subprocess.run(['python',str(O/'guard.py'),'fresh-'+n,*cmd],env=env)
 g=json.loads((O/('fresh-'+n+'.guard.json')).read_text());rows.append(g)
 if g['exit']!=0:break
(O/'replay-result.json').write_text(json.dumps({'modules':rows,'all_passed':len(rows)==5 and all(x['exit']==0 for x in rows),'trust_limit':'External prebuilt upstream oleans; no upstream rebuild.'},indent=2)+'\n')
