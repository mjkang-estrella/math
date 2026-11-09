from pathlib import Path
import hashlib,json,subprocess,sys,datetime
D=Path(__file__).resolve().parent
G=D.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
def rec(p):
 b=p.read_bytes();return dict(path=str(p.relative_to(D)),size=len(b),sha256=hashlib.sha256(b).hexdigest())
rows=[rec(p) for p in sorted(D.rglob('*')) if p.is_file() and p.name not in ['manifest.json','finalreceipt.json']]
m=D/'manifest.json';m.write_text(json.dumps(dict(excluded_exact_paths=['manifest.json','finalreceipt.json'],files=rows),indent=2)+'\n')
out=[]
for mode in ['', '--negative-hash','--negative-size','--negative-extra']:
 cmd=[sys.executable,'-B',str(G),sys.executable,'-B',str(D/'verify.py')]+([mode] if mode else [])
 r=subprocess.run(cmd,capture_output=True,text=True);out.append(dict(mode=mode or 'positive',exit=r.returncode,stdout=r.stdout,stderr=r.stderr));assert (r.returncode==0)==(mode=='')
b=m.read_bytes();receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=hashlib.sha256(b).hexdigest(),manifest_bytes=len(b),checks=out,recommendation='PARK_SOURCE_PRIOR_HOLD',ordinary_math='PASS v1 finite refutations',credit=0)
(D/'finalreceipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
