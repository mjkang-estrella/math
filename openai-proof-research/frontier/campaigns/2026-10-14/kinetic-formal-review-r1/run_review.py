#!/usr/bin/env python3
"""Independent fresh-copy compilation; writes only this review directory."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess
HERE=Path(__file__).resolve().parent
FROZEN=HERE.parent/'kinetic-formal-v1'
CACHE=HERE.parent/'formal/.lake/packages'
LEAN=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
EXPECTED_SOURCE='f4a419f9af0c2db04a54ac35f4ffcdebdd2db6aa1b246a5444c635357e735629'
EXPECTED_MANIFEST='e859674105795b9ef811ff35e4c6587f047f1a4705ecf1f4fa58c625fb2faf3b'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 assert sha(FROZEN/'KineticSupport.lean')==EXPECTED_SOURCE
 assert sha(FROZEN/'outputs.json')==EXPECTED_MANIFEST
 manifest=json.loads((FROZEN/'outputs.json').read_text())
 for row in manifest['files']:
  p=FROZEN/row['path'];assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes'],str(p)
 source=(FROZEN/'KineticSupport.lean').read_text()
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',source)
 # Read revision without invoking git or changing package metadata.
 gitdir=CACHE/'mathlib/.git'
 if gitdir.is_file():
  value=gitdir.read_text().strip().removeprefix('gitdir: ');gitdir=(gitdir.parent/value).resolve()
 head=(gitdir/'HEAD').read_text().strip()
 if head.startswith('ref: '):
  ref=head[5:];refpath=gitdir/ref
  if refpath.exists():revision=refpath.read_text().strip()
  else:revision=next(line.split()[0] for line in (gitdir/'packed-refs').read_text().splitlines() if line.endswith(' '+ref))
 else:revision=head
 assert revision=='d13f23b723b8a846827a245b89c10fc7d3f11612'
 version=subprocess.check_output([str(LEAN),'--version'],text=True).strip();assert '4.34.1' in version
 dependencies=[p/'.lake/build/lib/lean' for p in sorted(CACHE.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]
 build=HERE/'fresh';build.mkdir(exist_ok=True)
 for name in ['KineticSupport.lean','Checks.lean']:shutil.copyfile(FROZEN/name,build/name)
 shutil.copyfile(HERE/'TypedAudit.lean',build/'TypedAudit.lean')
 olean=build/'KineticSupport.olean'
 if olean.exists():olean.unlink()
 env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([str(build)]+[str(p.resolve()) for p in dependencies])
 logs=HERE/'logs';logs.mkdir(exist_ok=True)
 results=[]
 for label,args in [('fresh-source',['-o','KineticSupport.olean','KineticSupport.lean']),('frozen-checks',['Checks.lean']),('independent-typed',['TypedAudit.lean'])]:
  run=subprocess.run([str(LEAN)]+args,cwd=build,env=env,text=True,capture_output=True)
  output=run.stdout+run.stderr;(logs/(label+'.txt')).write_text(output)
  assert run.returncode==0,output
  assert 'warning:' not in output and 'sorryAx' not in output,output
  axioms=re.findall(r'depends on axioms: \[([^\]]*)\]',output)
  for row in axioms:assert set(row.split(', '))<={'propext','Classical.choice','Quot.sound'}
  if label=='frozen-checks':assert len(axioms)==9
  if label=='independent-typed':assert len(axioms)==14
  results.append({'check':label,'exit_code':0,'warnings':0,'axiom_lists':len(axioms)})
 # Deliberately broken own copies. They must fail in actual Lean checking.
 changes={
  'right-sign':('w + (inner ℝ (v - w) n) • n','w - (inner ℝ (v - w) n) • n'),
  'sequential-right':('j (rightVelocity (u i) (u j) n)','j (rightVelocity (leftVelocity (u i) (u j) n) (u j) n)'),
  'wrong-exponent':('= 1 / 440 ∧','= 1 / 441 ∧'),
  'contact-origin-sign':('((a - shift • v) + (t + shift) • v) -','((a + shift • v) + (t + shift) • v) -')}
 mutation_results=[]
 for label,(old,new) in changes.items():
  assert source.count(old)==1,label
  p=build/('Mutation_'+label.replace('-','_')+'.lean');p.write_text(source.replace(old,new))
  run=subprocess.run([str(LEAN),p.name],cwd=build,env=env,text=True,capture_output=True)
  (logs/('mutation-'+label+'.txt')).write_text(run.stdout+run.stderr)
  assert run.returncode!=0,'mutation unexpectedly compiled: '+label
  mutation_results.append({'mutation':label,'exit_code':run.returncode,'expected':'rejected'})
 # Frozen files must remain byte-identical.
 for row in manifest['files']:assert sha(FROZEN/row['path'])==row['sha256']
 out={'status':'independent scoped Lean support PASS','source_sha256':EXPECTED_SOURCE,'frozen_manifest_sha256':EXPECTED_MANIFEST,'lean_version':version,'mathlib':revision,'dependency_paths':[str(p.resolve()) for p in dependencies],'fresh_olean_sha256':sha(olean),'positive_checks':results,'negative_mutations':mutation_results,'concrete_counterchecks':['nonunit normal energy fails','sequential use of new left velocity loses energy','wrong affine origin shift sign fails'],'standard_axioms_only':True,'author_olean_trusted':False,'cache_modified':False,'full_kinetic_theorem_formalized':False,'scope':'nine supporting algebra statements; explicit raw typed wrappers, old-velocity evaluation, three concrete semantic counterchecks','source_after_sha256':sha(FROZEN/'KineticSupport.lean')}
 (HERE/'validation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
