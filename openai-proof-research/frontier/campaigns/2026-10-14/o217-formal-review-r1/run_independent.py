#!/usr/bin/env python3
"""Independent source compilation and real CLI controls. Writes only here. MIT."""
from pathlib import Path
import hashlib,json,os,subprocess,sys,tempfile,shutil
R=Path(__file__).resolve().parent
P=R/'rebuild-copy'
CACHE=R.parent/'formal/.lake/packages'
LEAN='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
E=R/'evidence'; rows=[]
env=os.environ.copy(); env['PYTHONDONTWRITEBYTECODE']='1'
def run(name,cmd,cwd,want):
 p=subprocess.run(cmd,cwd=cwd,env=env,capture_output=True,text=True,timeout=300)
 (E/(name+'.stdout')).write_text(p.stdout); (E/(name+'.stderr')).write_text(p.stderr)
 assert (p.returncode==0)==want,(name,p.stdout,p.stderr)
 rows.append({'name':name,'exit_code':p.returncode,'command':cmd})
 return p
with tempfile.TemporaryDirectory(prefix='.independent-',dir=R) as td:
 d=Path(td)
 for name in ['O217.lean']:
  shutil.copyfile(P/name,d/name)
 for name in ['IndependentControls.lean','NonincidentMutant.lean']:
  shutil.copyfile(R/name,d/name)
 lock=json.loads((P/'lake-manifest.json').read_text())
 env['LEAN_PATH']=os.pathsep.join([str(d)]+[str(CACHE/p['name']/'.lake/build/lib/lean') for p in lock['packages'] if (CACHE/p['name']/'.lake/build/lib/lean').is_dir()])
 run('independent-support',[LEAN,'-o','O217.olean','O217.lean'],d,True)
 run('independent-controls',[LEAN,'-o','IndependentControls.olean','IndependentControls.lean'],d,True)
 p=run('independent-nonincident-mutant',[LEAN,'NonincidentMutant.lean'],d,False)
 assert 'unsolved goals' in p.stdout and '⊢ False' in p.stdout
 assert not any(x in p.stdout+p.stderr for x in ['unknown identifier','unknown module','unexpected token'])
for name,code,want in [('cli-zero-failure',"print('SOME FAIL')",False),('cli-stderr-failure',"import sys; print('FAILED', file=sys.stderr)",False),('cli-exit7','raise SystemExit(7)',False),('cli-clean',"print('clean control')",True)]:
 run(name,[sys.executable,'-B',str(P/'checked_run.py'),'--log-prefix',str(E/(name+'-child')),'--',sys.executable,'-c',code],R,want)
(R/'evidence/independent-controls.json').write_text(json.dumps({'result':'PASS','rows':rows,'new_mathematical_boundary':'n=2 empty-star implies actual cubic zero; nonincident sign mutant; zero bootstrap and negative z square; edge counts 0,1,2'},indent=2)+'\n')
print('Independent semantic and CLI controls passed')
