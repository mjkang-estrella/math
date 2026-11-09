from pathlib import Path
import subprocess,sys,json,hashlib
l=Path(__file__).resolve().parent
p=l/'extracted'
def run(tag,*args):
 r=subprocess.run([sys.executable,'-I','scripts/limited.py',tag,sys.executable,'-I',*args],cwd=p,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 print(r.stdout,flush=True)
 if r.returncode: sys.exit(r.returncode)
run('review-examples-5','scripts/compile.py','-o','ReviewerExamples.olean','ReviewerExamples.lean')
run('review-leanchecker-final','scripts/check.py','PDTAR.FinalComplete')
run('review-declaration-audit','scripts/compile.py','scripts/Audit.lean')
