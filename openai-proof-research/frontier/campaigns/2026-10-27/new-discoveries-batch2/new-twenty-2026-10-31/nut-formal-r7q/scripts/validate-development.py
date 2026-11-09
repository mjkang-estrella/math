from pathlib import Path
import os,json,subprocess,sys,time,re
r=Path(__file__).resolve().parents[1];lean=Path(os.environ['LEAN_BIN']);pk=Path(os.environ['LEAN_PACKAGES'])
env={'PATH':str(lean.parent)+':/usr/bin:/bin','HOME':str(r/'home'),'TMPDIR':str(r/'tmp'),'MALLOC_ARENA_MAX':'2','PYTHONDONTWRITEBYTECODE':'1','LEAN_BIN':str(lean),'LEAN_PACKAGES':str(pk),'LEAN_PATH':':'.join([str(r/'formal')]+[str(p/'.lake/build/lib/lean') for p in sorted(pk.iterdir())])}
sf=r/'development-validation.json';state=json.loads(sf.read_text()) if sf.exists() else {'mode':'DEVELOPMENT_ONLY','done':{}}
jobs=[('checker:Nut8Final',[lean.parent/'leanchecker','Nut8Final'],0)]
jobs += [('audit:'+m,[lean,'-j1','-DwarningAsError=true',r/'formal'/(m+'.lean')],0) for m in json.loads((r/'audit-modules.json').read_text())]
for name,src in json.loads((r/'negative-controls.json').read_text()).items():
 p=r/'tmp'/(name+'.lean');p.write_text(src);jobs.append(('negative:'+name,[lean,'-j1','-DwarningAsError=true',p],1))
jobs.append(('negative:ExistingOlean',[sys.executable,'-I',r/'replay.py','--init-only'],1))
for key,cmd,expected in jobs:
 if key in state['done']:continue
 log=r/'logs'/f'{time.time_ns()}-dev-{key.replace(":","-")}.log'
 rc=subprocess.run([sys.executable,'-I',r/'scripts/capped.py',log]+list(map(str,cmd)),cwd=r,env=env,stdout=subprocess.DEVNULL).returncode
 receipt=json.loads(Path(str(log)+'.json').read_text())
 if (expected==0 and rc!=0) or (expected==1 and (rc==0 or receipt['cap_reason'])):
  print(log.read_text()[-8000:],flush=True);raise SystemExit('FAILED '+key+' '+str(log))
 rec={'receipt':str(log.relative_to(r))+'.json'}
 if key.startswith('audit:'):
  counts=re.findall(r'LOCAL_TOTAL (\d+)',log.read_text());assert len(counts)==1;rec['declarations']=int(counts[0]);assert rec['declarations']>0
 if key=='negative:ExistingOlean':assert 'Refusing existing oleans' in log.read_text()
 state['done'][key]=rec;sf.write_text(json.dumps(state,indent=2)+'\n');print('PASS DEVELOPMENT',key,flush=True)
state['status']='PASS_DEVELOPMENT_ONLY';state['audit_declarations']=sum(x.get('declarations',0) for x in state['done'].values());sf.write_text(json.dumps(state,indent=2)+'\n')
