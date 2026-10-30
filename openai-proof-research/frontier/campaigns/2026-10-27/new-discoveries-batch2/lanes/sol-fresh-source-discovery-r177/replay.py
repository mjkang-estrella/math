import subprocess,sys,hashlib,json,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
rows=[]
for script,out in [('checks.py','checks.json'),('tree_route.py','tree-route.json')]:
 before=(L/out).read_bytes() if (L/out).exists() else None
 p=subprocess.run([sys.executable,str(L/script)],capture_output=True,text=True)
 (L/(script+'.stdout.txt')).write_text(p.stdout);(L/(script+'.stderr.txt')).write_text(p.stderr)
 assert p.returncode==0,(script,p.stderr)
 after=(L/out).read_bytes();assert before is None or before==after
 rows.append(dict(script=script,output=out,sha256=hashlib.sha256(after).hexdigest(),byte_identical=before==after,exit=p.returncode))
(L/'replay-receipt.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),records=rows),indent=2)+'\n')
print(rows)
