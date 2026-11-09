"""Portable sequential replay. --init; repeated --step; --finish, or no args."""
from pathlib import Path
import os,sys,subprocess,json,hashlib
r=Path(__file__).resolve().parent;os.chdir(r)
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def sources():return {str(p.relative_to(r)):h(p) for d in ['formal','scripts','checks','negative-controls'] for p in sorted((r/d).rglob('*')) if p.is_file() and p.suffix in ['.lean','.py','.json']}|{'replay.py':h(r/'replay.py')}
def config():
 lean=Path(os.environ['LEAN_BIN']).resolve();packages=Path(os.environ['LEAN_PACKAGES']).resolve()
 env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN','LAKE'))};env['PATH']=str(lean.parent)+os.pathsep+os.defpath
 env.update(LEAN_PATH=':'.join([str(r/'formal')]+[str(p/'.lake/build/lib/lean') for p in sorted(packages.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]),MALLOC_ARENA_MAX='2',PYTHONDONTWRITEBYTECODE='1',HOME=str(r/'empty-home'),TMPDIR=str(r/'tmp'))
 return lean,env
mods=json.loads((r/'scripts/modules.json').read_text())
def plan(lean):
 calls=[('version',[str(lean),'--version'],False)]
 calls += [('replay-'+m,[str(lean),'-j1','-DwarningAsError=true','-o','formal/'+m+'.olean','formal/'+m+'.lean'],False) for m in mods]
 calls += [('leanchecker-'+m,[str(lean.with_name('leanchecker')),m],False) for m in mods]
 calls += [('negative-'+p.stem,[str(lean),'-j1','-DwarningAsError=true',str(p.relative_to(r))],True) for p in sorted((r/'negative-controls').glob('*.lean'))]
 calls += [('auditor-safety',[str(lean),'-j1','-DwarningAsError=true','checks/AuditToolSafety.lean'],False)]
 return calls
state=r/'replay-state.json'
def init():
 if any(r.rglob('*.olean')):raise SystemExit('REFUSED: existing .olean files; extract a fresh source-only packet')
 if state.exists():raise SystemExit('REFUSED: existing replay state')
 for d in ['logs','empty-home','tmp']:(r/d).mkdir(exist_ok=True)
 lean,env=config();save(state,{'sources':sources(),'lean':str(lean),'packages':str(Path(os.environ['LEAN_PACKAGES']).resolve()),'completed':[],'oleans':{}})
 print('INITIALIZED clean source-only replay',flush=True)
def step():
 s=json.loads(state.read_text());assert s['sources']==sources(),'source mutation'
 lean,env=config();assert s['lean']==str(lean) and s['packages']==str(Path(os.environ['LEAN_PACKAGES']).resolve())
 calls=plan(lean);i=len(s['completed'])
 if i==len(calls):print('DONE');return False
 name,cmd,negative=calls[i];log='logs/'+name+'.log'
 rc=subprocess.run([sys.executable,'-I','scripts/watchdog.py',log,*cmd],env=env).returncode
 receipt=json.loads(Path(log+'.receipt.json').read_text())
 ok=(rc==1 and receipt['killed'] is None and 'error:' in Path(log).read_text()) if negative else rc==0
 if name=='version':ok=ok and '4.34.1' in Path(log).read_text() and '5045d0056413266e57c625dcd7c365b10e377c52' in Path(log).read_text()
 if not ok:raise SystemExit('FAIL: '+name)
 s['completed'].append({'name':name,'exit_code':rc,'expected_failure':negative})
 if name.startswith('replay-'):
  p=r/'formal'/(name[7:]+'.olean');s['oleans'][str(p.relative_to(r))]=h(p)
 save(state,s);print('STEP',i+1,'/',len(calls),name,'PASS',flush=True);return True
def finish():
 s=json.loads(state.read_text());lean,env=config();calls=plan(lean)
 assert len(s['completed'])==len(calls) and s['sources']==sources()
 assert all(h(r/p)==v for p,v in s['oleans'].items())
 # Original clean driver must reject this compiled extraction, before version/build calls.
 q=subprocess.run([sys.executable,'-I','scripts/replay.py'],capture_output=True,text=True,env=os.environ.copy())
 (r/'logs/negative-existing-olean.log').write_text(q.stdout+q.stderr)
 assert q.returncode and 'REFUSED: existing .olean' in q.stderr
 negative=[{'name':v['name'][9:],'exit_code':v['exit_code'],'rejected':True} for v in s['completed'] if v['expected_failure']]
 negative.append({'name':'existing-olean','exit_code':q.returncode,'rejected':True})
 save(r/'negative-results.json',{'checks':negative,'passed':True})
 save(r/'auditor-safety-receipt.json',{'passed':True,'exit_code':0,'log':'logs/auditor-safety.log'})
 save(r/'replay-receipt.json',{'passed':True,'checks':s['completed'][:539],'formal_source_sha256':{str(p.relative_to(r)):h(p) for p in sorted((r/'formal').glob('*.lean'))},'orchestration':'resumable one guarded subprocess per --step; initialized with no oleans','total_guarded_calls':len(calls)})
 print('PASS: strict rebuild, one-module kernel checks, full AuditR5, negative controls and auditor safety',flush=True)
if __name__=='__main__':
 mode=sys.argv[1] if len(sys.argv)>1 else '--all'
 if mode=='--init':init()
 elif mode=='--step':step()
 elif mode=='--finish':finish()
 elif mode=='--all':
  init()
  while step():pass
  finish()
 else:raise SystemExit('Use --init, --step, --finish, or no args')
