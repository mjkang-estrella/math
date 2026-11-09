from pathlib import Path
import os,sys,json,hashlib,subprocess,tempfile,shutil
D=Path(__file__).resolve().parents[1]
B=Path(os.environ['LEAN_BIN']).resolve(); P=Path(os.environ['LEAN_PACKAGES']).resolve()
os.environ['PATH']=str(B)+os.pathsep+os.environ.get('PATH','')
R=D/'replay-receipts';R.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not list(D.rglob('*.olean')), 'Refusing pre-existing local oleans'
pins=json.loads((D/'DEPENDENCIES.json').read_text())
manifest=json.loads((D/'source-manifest.json').read_text())
for f,h in manifest.items():assert sha(D/f)==h, f
assert sha(D/'proof/Hierarchy.lean')=='b3b62b05aa010d06c98455035dfd752a60de56a7fcba03d4cf532d383786ec8b'
T=Path(tempfile.mkdtemp(prefix='replay-owned-',dir=D));commands=[]
def run(label,args,ok=True):
 subprocess.run([sys.executable,'-I',str(D/'tools/capped.py'),str(R),label,str(T),'--',*map(str,args)],check=True)
 r=json.loads((R/(label+'.receipt.json')).read_text());commands.append(r)
 assert r['killed_reason'] is None,label
 assert (r['exit']==0)==ok,label
 return (R/(label+'.log')).read_text()
try:
 v=run('version',[B/'lean','--version'])
 assert pins['Lean'] in v and pins['Lean_commit'] in v,v
 lm=P.parent.parent/'lake-manifest.json'
 assert lm.exists(), 'Need parent lake-manifest.json'
 pk=json.loads(lm.read_text())['packages']
 assert any(x['name']=='mathlib' and x['rev']==pins['mathlib'] for x in pk)
 cache_before=sha(lm)
 libs=sorted(P.glob('*/.lake/build/lib/lean'));assert libs
 os.environ['LEAN_PATH']=str(T)+os.pathsep+os.pathsep.join(map(str,libs))
 lean=[B/'lean','-j1','-DwarningAsError=true']
 for name in ['Hierarchy','AllAudit','ReviewSanity']:
  shutil.copyfile(D/'proof'/(name+'.lean'),T/(name+'.lean'))
  txt=run('build-'+name,[*lean,'-o',T/(name+'.olean'),T/(name+'.lean')])
  if name=='AllAudit':assert 'TOTAL 101' in txt
  run('kernel-'+name,[B/'leanchecker','-j1',name])
 (T/'NegativeFalse.lean').write_text('import Hierarchy\nexample : False := Supervenience.literal_conjecture_false\n')
 txt=run('negative-false',[*lean,T/'NegativeFalse.lean'],False);assert 'error:' in txt
 (T/'NegativeSorry.lean').write_text('import Hierarchy\nexample : False := by sorry\n')
 txt=run('negative-sorry',[*lean,T/'NegativeSorry.lean'],False);assert 'sorry' in txt
 (T/'Hierarchy.lean').write_text((D/'proof/Hierarchy.lean').read_text()+'\naxiom DeliberateAuditControl : True\n')
 run('negative-axiom-compile',[*lean,'-o',T/'Hierarchy.olean',T/'Hierarchy.lean'])
 txt=run('negative-axiom-audit',[*lean,T/'AllAudit.lean'],False)
 assert 'bad declaration DeliberateAuditControl' in txt,txt[-2000:]
 assert sha(lm)==cache_before
 for f,h in manifest.items():assert sha(D/f)==h,f
 (R/'replay.json').write_text(json.dumps({'status':'PASS','commands':len(commands),'declarations':101,'allowed_axioms':['propext','Classical.choice','Quot.sound'],'Hierarchy_sha256':sha(D/'proof/Hierarchy.lean'),'cache_manifest_unchanged':True,'negative_controls':'false proof rejected; sorry rejected under warningAsError; injected local axiom rejected by module-origin audit','trust':pins['trust']},indent=2)+'\n')
finally:
 shutil.rmtree(T) # Only the fresh directory owned by this invocation.
