"""Small independently manifested selected-copy controls, all inside own root."""
from pathlib import Path
import hashlib,json,os,shutil,stat,subprocess,sys
from seal import make
own=Path.cwd()/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r121';control=own/'packet/private/controls';case=control/'case';case.mkdir(parents=True,exist_ok=False);(case/'packet').mkdir()
sources=[own/'packet/notes/feasibility.md',own/'packet/private/source/section-08-global-sections.tex',own/'packet/code/verify.py']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
old={str(p):sha(p) for p in sources}
for p in sources:shutil.copyfile(p,case/'packet'/p.name)
(case/'FINAL.md').write_text('Reduced copied integrity control only; no mathematical grade.\n')
(case/'REPORT.md').write_text('This selection has its OWN manifest; no inherited original manifest.\n')
make(case)
anchors={x:sha(case/x) for x in ['FINAL.md','MANIFEST.json','REPORT.md']}
def snap():
 d={}
 for b,ds,fs in os.walk(case,followlinks=False):
  for n in ds+fs:
   p=Path(b)/n;s=p.lstat();d[p.relative_to(case).as_posix()]=[s.st_mode,s.st_nlink,s.st_size if p.is_file() else None,sha(p) if p.is_file() else None]
 return d
results=[]
def check(label,ok,aa=None):
 before=snap();a=aa or anchors
 cmd=[sys.executable,'-B',str(own/'packet/code/verify.py'),str(case),'--final-sha256',a['FINAL.md'],'--manifest-sha256',a['MANIFEST.json'],'--report-sha256',a['REPORT.md']]
 r=subprocess.run(cmd,capture_output=True,text=True,cwd=Path.cwd());after=snap()
 assert before==after,'verifier mutated copied case';assert (r.returncode==0)==ok,(label,r.stdout,r.stderr)
 results.append({'case':label,'expected_accept':ok,'exit_code':r.returncode,'read_only':True,'output':r.stdout.strip()})
check('baseline',True)
p=case/'packet/feasibility.md';b=p.read_bytes();p.write_bytes(b+b'corruption\n');check('modified payload',False);p.write_bytes(b)
p.unlink();check('missing payload',False);p.write_bytes(b)
p=case/'packet/.extra';p.write_text('unexpected');check('hidden extra',False);p.unlink()
p=case/'packet/empty-extra';p.mkdir();check('extra empty directory',False);p.rmdir()
a=dict(anchors);a['MANIFEST.json']='0'*64;check('wrong detached manifest',False,a)
check('restored',True)
assert {str(p):sha(p) for p in sources}==old
(control/'results.json').write_text(json.dumps({'selected_original_hashes':old,'own_fixture_anchors':anchors,'results':results,'originals_unchanged':True,'scope':'artifact behavior only; neither mathematics nor independent review'},indent=2))
print(json.dumps({'copied_cases':len(results),'expected_outcomes':True,'read_only':True,'selected_originals_unchanged':True}))
