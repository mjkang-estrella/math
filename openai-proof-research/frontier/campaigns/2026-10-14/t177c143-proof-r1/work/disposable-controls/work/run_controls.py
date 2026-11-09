from pathlib import Path
import hashlib,json,subprocess,sys,os
R=Path(__file__).resolve().parents[1]
F=R/'packet/private/copied-controls/fixture'
F.mkdir(parents=True,exist_ok=True)
(F/'verify.py').write_bytes((R/'packet/public/verify.py').read_bytes())
(F/'toy.txt').write_text('Copied integrity control, not mathematical evidence.\n')
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
rows=[{'path':p.name,'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in sorted(F.iterdir()) if p.name in ['verify.py','toy.txt']]
dump(F/'MANIFEST.json',{'format':'r143-exact-files-v1','files':rows})
(F/'REPORT.md').write_text('Synthetic copied control only.\n')
dump(F/'FINAL.json',{'manifest_sha256':sha((F/'MANIFEST.json').read_bytes()),'report_sha256':sha((F/'REPORT.md').read_bytes()),'verifier_path':'verify.py','verifier_sha256':sha((F/'verify.py').read_bytes())})
a={n:sha((F/n).read_bytes()) for n in ['FINAL.json','MANIFEST.json','REPORT.md']}
(F/'SHA256SUMS').write_text(''.join(a[n]+'  '+n+'\n' for n in a))
def snapshot():return {p.name:sha(p.read_bytes()) for p in F.iterdir() if p.is_file()}
receipts=[]
def run(name,accept,anchors=None):
 anchors=anchors or a
 before=snapshot()
 cmd=[sys.executable,str(F/'verify.py'),str(F)]
 for f,flag in [('FINAL.json','--final-sha256'),('MANIFEST.json','--manifest-sha256'),('REPORT.md','--report-sha256')]:cmd +=[flag,anchors[f]]
 r=subprocess.run(cmd,capture_output=True,text=True,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'},timeout=20)
 assert (r.returncode==0)==accept,(name,r.stdout,r.stderr)
 assert before==snapshot(),'verifier wrote files'
 receipts.append({'case':name,'expected_accept':accept,'returncode':r.returncode,'stdout':r.stdout.strip(),'before_after_bytes_equal':True})
run('baseline',True)
old=(F/'toy.txt').read_bytes();(F/'toy.txt').write_bytes(old+b'tamper\n');run('tampered payload',False);(F/'toy.txt').write_bytes(old)
(F/'extra.txt').write_text('extra\n');run('extra member',False);(F/'extra.txt').unlink()
for n in a:run('bad detached '+n,False,{**a,n:'0'*64})
run('restored baseline',True)
dump(R/'packet/private/copied-controls/results.json',{'meaning':'Copied synthetic artifact checks only; no original altered, no mathematical gate.','cases':receipts})
print(json.dumps(receipts,indent=2))
