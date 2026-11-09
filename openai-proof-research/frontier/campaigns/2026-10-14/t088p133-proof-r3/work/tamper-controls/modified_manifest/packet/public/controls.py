#!/usr/bin/env python3
"""MIT. Bounded copied-packet integrity controls. Writes only under this review root.
This is not a mathematical checker. Run before sealing; it writes the results payload.
"""
import hashlib,importlib.util,json,shutil,sys
from pathlib import Path
sys.dont_write_bytecode=True
R=Path(__file__).resolve().parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,j):p.write_text(json.dumps(j,indent=2,sort_keys=True)+'\n')
def seal_fixture(p):
 files={str(q.relative_to(p)):{'bytes':q.stat().st_size,'sha256':sha(q)} for q in (p/'packet').rglob('*') if q.is_file() and q.name!='MANIFEST.json'}
 dirs=sorted(str(q.relative_to(p)) for q in (p/'packet').rglob('*') if q.is_dir())
 dump(p/'packet/MANIFEST.json',{'files':files,'directories':dirs})
 dump(p/'FINAL.json',{'manifest_sha256':sha(p/'packet/MANIFEST.json'),'outside_report_sha256':sha(p/'REPORT.md'),'verdict':'PASS_FULL_T088P133','review_sha256':sha(p/'packet/public/review.md'),'verdict_sha256':sha(p/'packet/public/verdict.json')})
 return [sha(p/'FINAL.json'),sha(p/'packet/MANIFEST.json'),sha(p/'REPORT.md')]
def main():
 work=R/'work/tamper-controls';work.mkdir(parents=True,exist_ok=False)
 spec=importlib.util.spec_from_file_location('readonly_verifier',R/'packet/public/verify.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
 fixture=work/'baseline';fixture.mkdir();shutil.copytree(R/'packet',fixture/'packet')
 (fixture/'REPORT.md').write_text('Copied fixture report; not an external theorem verdict.\n')
 anchors=seal_fixture(fixture)
 # Exact non-hardlinked copies of the bound originals, including previous pycache.
 originals=work/'copied-originals';originals.mkdir()
 bindings=json.loads((R/'packet/private/original-bindings-start.json').read_text())
 repo=R.parents[3]
 for rel,m in bindings.items():
  target=originals/rel
  if m['type']=='dir':target.mkdir(parents=True,exist_ok=True);target.chmod(m['mode'])
  else:target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(repo/rel,target)
 results=[]
 def run(name,mutation=None,expected=True,orig=originals):
  case=work/name;shutil.copytree(fixture,case)
  if mutation:mutation(case)
  try:v.verify(case,*anchors,orig);passed=True;error=None
  except (ValueError,KeyError,OSError) as e:passed=False;error=str(e)
  assert passed==expected,(name,passed,error)
  results.append(dict(case=name,expected_accept=expected,accepted=passed,result='PASS',rejection=error))
 run('clean_copy')
 run('modified_payload',lambda p:(p/'packet/public/review.md').write_text('tamper\n'),False)
 run('deleted_payload',lambda p:(p/'packet/public/verdict.json').unlink(),False)
 run('extra_payload',lambda p:(p/'packet/public/EXTRA').write_text('extra\n'),False)
 def link(p):
  q=p/'packet/public/review.md';q.unlink();q.symlink_to(p/'packet/public/verdict.json')
 run('linked_payload',link,False)
 run('modified_outside_report',lambda p:(p/'REPORT.md').write_text('tamper\n'),False)
 run('modified_manifest',lambda p:(p/'packet/MANIFEST.json').write_text('{}\n'),False)
 run('modified_final',lambda p:(p/'FINAL.json').write_text('{}\n'),False)
 def reseal(p):
  (p/'packet/public/review.md').write_text('tampered and locally resealed\n');seal_fixture(p)
 run('forged_local_reseal',reseal,False)
 # Mutate only a copied original. The genuine originals are never mutation targets.
 first=next(p for p,m in bindings.items() if m['type']=='file')
 (originals/first).write_bytes((originals/first).read_bytes()+b'\nTAMPER\n')
 run('changed_copied_original',None,False)
 dump(R/'packet/public/checks/tamper-controls.json',{'artifact_tests_only':True,'cases':results,'all_expected_outcomes':True,'actual_originals_never_mutated':True})
 print(json.dumps(results,indent=2))
if __name__=='__main__':main()
