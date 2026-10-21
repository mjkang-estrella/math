from pathlib import Path
import hashlib,json,shutil,subprocess,sys
from seal import seal,ROOT
from verify import verify
D=ROOT/'private/reduced-control';D.mkdir()
sources={'calculation.md':ROOT/'notes/01-prefreeze-calculations.md','diagnostic.py':ROOT/'code/graded_boundary.py','source-section.tex':ROOT/'private/source/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/build/sections/02-graphs.tex','verify.py':ROOT/'code/verify.py'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
before={str(p.relative_to(ROOT)):sha(p) for p in sources.values()}
for name,p in sources.items():shutil.copyfile(p,D/name)
anchors=seal(D,'Reduced copy control; selected local bytes only.','Reduced copy has its OWN fresh manifest. Incoming originals are authenticated separately.')
def snap():return {str(p.relative_to(D)):sha(p) for p in D.rglob('*') if p.is_file()}
def check(expect):
 old=snap();args=[sys.executable,str(D/'verify.py'),'--root',str(D),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']]
 p=subprocess.run(args,capture_output=True,text=True,env={'PYTHONDONTWRITEBYTECODE':'1','PATH':'/usr/bin:/bin'})
 assert (p.returncode==0)==expect,(p.returncode,p.stdout,p.stderr)
 assert old==snap(),'verifier wrote control copy'
 return {'exit_code':p.returncode,'read_only_observed':True,'expected_accept':expect,'output':(p.stdout+p.stderr).strip()}
results={'baseline':check(True)}
p=D/'calculation.md';orig=p.read_bytes();p.write_bytes(orig+b'changed\n');results['tamper']=check(False);p.write_bytes(orig)
p=D/'diagnostic.py';orig=p.read_bytes();p.unlink();results['missing']=check(False);p.write_bytes(orig)
p=D/'extra.txt';p.write_text('extra');results['extra']=check(False);p.unlink()
old=anchors['REPORT.md'];anchors['REPORT.md']='0'*64;results['wrong_detached_anchor']=check(False);anchors['REPORT.md']=old
results['restored']=check(True)
assert before=={str(p.relative_to(ROOT)):sha(p) for p in sources.values()},'selected originals changed'
(ROOT/'private/control-results.json').write_text(json.dumps({'reduced_copy_membership':list(sources),'fresh_reduced_copy_anchors':anchors,'selected_original_hashes_before_and_after':before,'results':results,'mathematical_gate':False},indent=2)+'\n')
print(json.dumps({'copied_controls':list(results),'selected_originals_unchanged':True,'mathematical_gate':False}))
