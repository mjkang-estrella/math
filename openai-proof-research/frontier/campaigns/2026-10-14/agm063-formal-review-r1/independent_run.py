import hashlib,json,os,re,subprocess,tempfile
from pathlib import Path
R=Path(__file__).resolve().parent
P=R/'rebuild-copy'
lean='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
cache=R.parent/'formal/.lake/packages'
out=R/'independent-logs';out.mkdir(exist_ok=True)
rows=[]
def run(label,args,cwd,env,ok=True):
 p=subprocess.run(args,cwd=cwd,env=env,text=True,capture_output=True)
 (out/(label+'.stdout')).write_text(p.stdout);(out/(label+'.stderr')).write_text(p.stderr)
 rows.append(dict(name=label,command=args,exit=p.returncode))
 assert (p.returncode==0)==ok,(label,p.stdout,p.stderr)
 return p
with tempfile.TemporaryDirectory(prefix='.review-compile-',dir=R) as tmp:
 t=Path(tmp);(t/'AGM063.lean').write_bytes((P/'AGM063.lean').read_bytes());(t/'Independent.lean').write_bytes((R/'Independent.lean').read_bytes())
 libs=[str(cache/x['name']/'.lake/build/lib/lean') for x in json.loads((P/'lake-manifest.json').read_text())['packages']]
 env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([str(t)]+libs);env['PYTHONDONTWRITEBYTECODE']='1'
 run('fresh-support',[lean,'-o','AGM063.olean','AGM063.lean'],t,env)
 run('independent-witnesses',[lean,'-o','Independent.olean','Independent.lean'],t,env)
 names=re.findall(r'^(?:def|theorem) (\w+)',(R/'Independent.lean').read_text(),re.M)
 (t/'Audit.lean').write_text('import Independent\n'+''.join(f'#check @Independent.{n}\n#print axioms Independent.{n}\n' for n in names))
 run('independent-types-axioms',[lean,'Audit.lean'],t,env)
 mutants={
 'minimum-degree':'example : Independent.badDegree true < 2 * 2 := by norm_num [Independent.badDegree]',
 'quotient-constancy':'example : (false,true) ∈ AGM063.fiberPairs (Set.univ : Set Bool) (fun x => x.val) := by simp [AGM063.fiberPairs]',
 'nonempty-span':'example : (LinearMap.id : ℝ →ₗ[ℝ] ℝ) 1 = 0 := by norm_num',
 'rational-multiplicity':'example : (3/2 : ℚ) = 1 := by norm_num',
 'rational-pseudoindex':'example : (5/2 : ℚ) = 2 := by norm_num'}
 for name,src in mutants.items():
  source='import Independent\n'+src+'\n';(out/(name+'.lean')).write_text(source);(t/'Mutant.lean').write_text(source)
  p=run(name,[lean,'Mutant.lean'],t,env,False)
  assert 'unsolved goals' in p.stdout or 'proved that the proposition' in p.stdout
  assert not any(s in p.stdout for s in ['unknown identifier','unknown module','unexpected token'])
(R/'independent-controls.json').write_text(json.dumps({'rows':rows,'result':'PASS_INDEPENDENT_BOUNDARIES'},indent=2)+'\n')
print('PASS_INDEPENDENT_BOUNDARIES')
