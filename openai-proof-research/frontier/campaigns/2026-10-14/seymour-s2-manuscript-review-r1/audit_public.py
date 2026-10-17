"""Independent manuscript public extraction tests. Original code MIT."""
from pathlib import Path
import hashlib,json,subprocess,sys,shutil
O=Path(__file__).resolve().parent; R=O/'tmp/public'; results={}
def run(name,script,ok=True,args=()):
 p=subprocess.run([sys.executable,'-B',str(R/script),*args],cwd=R,capture_output=True,text=True)
 results[name]={'returncode':p.returncode,'stdout':p.stdout,'stderr':p.stderr}
 assert (p.returncode==0)==ok,(name,p.returncode,p.stderr)
 return p
h='61b1616c12d79c2512f2e572b4184ea5e70d3c9f3c5f6ee345a9cbab43c2d2cf'
run('clean_integrity','support/verify_package.py',args=('--manifest-sha256',h))
p=run('clean_diagnostics','support/run_checks.py')
assert json.loads(p.stdout)==json.loads((R/'checks/finite-checks.json').read_text())
run('unchanged_after_execution','support/verify_package.py',args=('--manifest-sha256',h))
run('wrong_anchor','support/verify_package.py',False,('--manifest-sha256','0'*64))
for name,rel,content,script in [
 ('changed_tex','main.tex',b'changed','support/verify_package.py'),
 ('changed_checker','support/inherited/author.py',b'print("PASS")','support/run_checks.py'),
 ('missing_checker','support/inherited/reviewer.py',None,'support/run_checks.py'),
 ('missing_identities','checker-identities.json',None,'support/run_checks.py'),
 ('missing_formal_source','formal/SeymourSupport.lean',None,'support/verify_package.py'),
 ('missing_pdf','output/pdf/main.pdf',None,'support/verify_package.py')]:
 f=R/rel; old=f.read_bytes()
 try:
  if content is None:f.unlink()
  else:f.write_bytes(content)
  run(name,script,False)
 finally:f.write_bytes(old)
f=R/'support/run_checks.py';old=f.read_bytes()
try:
 f.write_bytes(old.replace(b"'deletion_endpoint_cases':15129",b"'deletion_endpoint_cases':15130"))
 assert f.read_bytes()!=old
 run('wrong_expected_result','support/run_checks.py',False)
finally:f.write_bytes(old)
f=R/'public-manifest.json';old=f.read_bytes()
for name,mut in [('duplicate_path',lambda m:m['files'].append(m['files'][0].copy())),('parent_path',lambda m:m['files'][0].update(path='../escape')),('absolute_path',lambda m:m['files'][0].update(path='/tmp/escape')),('noncanonical_path',lambda m:m['files'][0].update(path='formal//Controls.lean'))]:
 try:
  m=json.loads(old);mut(m);f.write_text(json.dumps(m));run(name,'support/verify_package.py',False)
 finally:f.write_bytes(old)
key='support/inherited/reviewer.py';g=R/key;before=g.read_bytes()
try:
 m=json.loads(old);m['files']=[r for r in m['files'] if r['path']!=key];f.write_text(json.dumps(m));g.unlink();run('omitted_required_anchor','support/verify_package.py',False)
finally:f.write_bytes(old);g.write_bytes(before)
g=R/'unlisted.txt';g.write_text('test')
try:run('unlisted_payload','support/verify_package.py',False)
finally:g.unlink()
g=R/'main.tex';old=g.read_bytes();g.unlink();g.symlink_to('README.md')
try:run('symlink','support/verify_package.py',False)
finally:g.unlink();g.write_bytes(old)
run('restored_integrity','support/verify_package.py',args=('--manifest-sha256',h))
(O/'public-test-results.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps({'status':'PASS_INDEPENDENT_PUBLIC_TESTS','scenarios':len(results)}))
