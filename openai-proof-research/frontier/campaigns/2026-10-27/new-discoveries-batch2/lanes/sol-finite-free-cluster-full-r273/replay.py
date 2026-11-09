import subprocess,sys,json,time
from pathlib import Path
L=Path(__file__).resolve().parent
out=[]
for args in [['symbolic.py'],['cluster.py','--moderate'],['cluster.py'],['threecluster.py']]:
 t=time.monotonic();p=subprocess.run([sys.executable,str(L/args[0])]+args[1:],capture_output=True,text=True)
 out.append(dict(args=args,exit=p.returncode,stdout=p.stdout,stderr=p.stderr,wall=time.monotonic()-t));assert p.returncode==0
(L/'replay-results.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
