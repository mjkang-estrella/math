from pathlib import Path
import hashlib,json,subprocess,sys,os
R=Path(__file__).resolve().parents[1]
F=R/'work/review-control-copy'
F.mkdir(exist_ok=True)
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(p,o):p.write_text(json.dumps(o,indent=2)+'\n')
(F/'verify.py').write_bytes((R/'packet/public/verify.py').read_bytes())
(F/'review.md').write_text('Disposable synthetic artifact only.\n')
rows=[{'path':n,'bytes':len((F/n).read_bytes()),'sha256':sha((F/n).read_bytes())} for n in ['review.md','verify.py']]
dump(F/'MANIFEST.json',{'format':'t177c143-contribution-r1-exact-v1','files':rows})
(F/'REPORT.md').write_text('Synthetic report.\n')
dump(F/'FINAL.json',{'manifest_sha256':sha((F/'MANIFEST.json').read_bytes()),'report_sha256':sha((F/'REPORT.md').read_bytes()),'verifier_path':'verify.py','verifier_sha256':sha((F/'verify.py').read_bytes()),'review_path':'review.md','review_sha256':sha((F/'review.md').read_bytes())})
a={n:sha((F/n).read_bytes()) for n in ['FINAL.json','MANIFEST.json','REPORT.md']}
(F/'SHA256SUMS').write_text(''.join(a[n]+'  '+n+'\n' for n in a))
def snapshot():return {p.name:sha(p.read_bytes()) for p in F.iterdir() if p.is_file()}
results=[]
def run(case,accept,anchors=None):
 h=anchors or a;before=snapshot();cmd=[sys.executable,str(F/'verify.py'),str(F)]
 for n,flag in [('FINAL.json','--final-sha256'),('MANIFEST.json','--manifest-sha256'),('REPORT.md','--report-sha256')]:cmd.extend([flag,h[n]])
 r=subprocess.run(cmd,capture_output=True,text=True,timeout=15,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1','TMPDIR':str(R/'work')})
 if (r.returncode==0)!=accept or snapshot()!=before:raise RuntimeError(case)
 results.append({'case':case,'expected_accept':accept,'returncode':r.returncode,'stdout':r.stdout.strip(),'per_call_bytes_unchanged':True})
run('baseline',True)
p=F/'review.md';old=p.read_bytes();p.write_bytes(old+b'tamper');run('payload mutation',False);p.write_bytes(old)
p=F/'extra';p.write_text('extra');run('extra file',False);p.unlink()
for n in a:run('wrong '+n,False,{**a,n:'0'*64})
run('restored baseline',True)
dump(R/'private/review-controls.json',{'meaning':'Seven disposable artifact controls only, no mathematical gate.','cases':results})
print('Seven copied reviewer-verifier controls behaved as expected.')
