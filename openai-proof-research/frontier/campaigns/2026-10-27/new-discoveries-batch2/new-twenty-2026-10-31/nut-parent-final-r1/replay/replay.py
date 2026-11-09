#!/usr/bin/env python3
"""Fresh init refuses oleans; --resume validates recorded progress. One heavy child at a time."""
import os,sys,json,hashlib,subprocess,time,re,argparse
from pathlib import Path
r=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--resume',action='store_true');p.add_argument('--steps',type=int,default=1);p.add_argument('--init-only',action='store_true');p.add_argument('--development',action='store_true');a=p.parse_args()
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((r/'source-manifest.json').read_text())
for f,d in manifest.items():
 if h(r/f)!=d:raise SystemExit('Source hash mismatch: '+f)
sf=r/('development-state.json' if a.development else 'replay-state.json')
mods=json.loads((r/'modules.json').read_text());audits=json.loads((r/'audit-modules.json').read_text());controls=json.loads((r/'negative-controls.json').read_text())
for d in ['logs','tmp','home']:(r/d).mkdir(exist_ok=True)
lean=Path(os.environ['LEAN_BIN']).resolve();pk=Path(os.environ['LEAN_PACKAGES']).resolve()
env={'PATH':str(lean.parent)+':/usr/bin:/bin','HOME':str(r/'home'),'TMPDIR':str(r/'tmp'),'MALLOC_ARENA_MAX':'2','PYTHONDONTWRITEBYTECODE':'1','LEAN_BIN':str(lean),'LEAN_PACKAGES':str(pk),'LEAN_PATH':':'.join([str(r/'formal')]+[str(x/'.lake/build/lib/lean') for x in sorted(pk.iterdir())])}
if not a.resume:
 if not a.development and list(r.rglob('*.olean')):raise SystemExit('Refusing existing oleans; extract a fresh source-only packet.')
 if sf.exists():raise SystemExit('Refusing existing state; use --resume')
 state={'mode':'DEVELOPMENT' if a.development else 'FRESH','sources':h(r/'source-manifest.json'),'done':{},'status':'IN_PROGRESS'}
 if a.development:
  for m in mods:
   f=r/'formal'/(m+'.olean')
   if f.exists():state['done']['build:'+m]={'olean_sha256':h(f),'cached':True}
 sf.write_text(json.dumps(state,indent=2)+'\n')
else:
 state=json.loads(sf.read_text());assert state['sources']==h(r/'source-manifest.json')
 for key,v in state['done'].items():
  if key.startswith('build:'):assert h(r/'formal'/(key.split(':',1)[1]+'.olean'))==v['olean_sha256'],key
 # Refuse any unrecorded object, preventing accidental cache injection.
 known={key.split(':',1)[1] for key in state['done'] if key.startswith('build:')}
 for f in (r/'formal').glob('*.olean'):assert f.stem in known,('Unrecorded olean',f)
if a.init_only:raise SystemExit(0)
jobs=[('build:'+m,[lean,'-j1','-DwarningAsError=true','-o',r/'formal'/(m+'.olean'),r/'formal'/(m+'.lean')],0) for m in mods]
if not a.development:
 jobs += [('checker:'+m,[lean.parent/'leanchecker',m],0) for m in mods]
 jobs += [('audit:'+m,[lean,'-j1','-DwarningAsError=true',r/'formal'/(m+'.lean')],0) for m in audits]
 for name,source in controls.items():
  f=r/'tmp'/(name+'.lean');f.write_text(source)
  jobs.append(('negative:'+name,[lean,'-j1','-DwarningAsError=true',f],1))
 # Same fresh refusal must run before source validation (manifest remains identical).
 jobs.append(('negative:ExistingOlean',[sys.executable,'-I',r/'replay.py','--init-only'],1))
steps=0
for key,cmd,expected in jobs:
 if key in state['done']:continue
 log=r/'logs'/f'{time.time_ns()}-{key.replace(":","-")}.log'
 rc=subprocess.run([sys.executable,'-I',r/'scripts/capped.py',log]+list(map(str,cmd)),cwd=r,env=env,stdout=subprocess.DEVNULL).returncode
 receipt=json.loads(Path(str(log)+'.json').read_text())
 if (expected==0 and rc!=0) or (expected==1 and (rc==0 or receipt['cap_reason'])):
  print(log.read_text()[-8000:]);print('FAILED',key,log,flush=True);raise SystemExit(1)
 if key=='negative:ExistingOlean' and 'Refusing existing' not in log.read_text():raise SystemExit('Wrong refusal reason')
 record={'receipt':str(log.relative_to(r))+'.json'}
 if key.startswith('build:'):record['olean_sha256']=h(r/'formal'/(key.split(':',1)[1]+'.olean'))
 if key.startswith('audit:'):
  text=log.read_text();counts=re.findall(r'LOCAL_TOTAL (\d+)',text);assert len(counts)==1,key
  record['declarations']=int(counts[0]);assert record['declarations']>0
 state['done'][key]=record;sf.write_text(json.dumps(state,indent=2)+'\n')
 print('PASS',key,flush=True);steps+=1
 if steps>=a.steps:break
if all(key in state['done'] for key,_,_ in jobs):
 state['status']='PASS_DEVELOPMENT' if a.development else 'PASS';state['audit_declarations']=sum(v.get('declarations',0) for v in state['done'].values());sf.write_text(json.dumps(state,indent=2)+'\n');print(state['status'])
