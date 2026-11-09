import json,subprocess,sys,resource
from pathlib import Path
p=Path(__file__).resolve().parent
resource.setrlimit(resource.RLIMIT_FSIZE,(512*1024*1024,512*1024*1024))
for m in json.loads((p/'dependency-order.json').read_text()):
 print('BUILD '+m,flush=True)
 with (p/'formal'/(m+'.driver.log')).open('w') as f:
  r=subprocess.run([sys.executable,'guard.py',m+'.lean.log','-o',m+'.olean',m+'.lean'],cwd=p/'formal',stdout=f,stderr=subprocess.STDOUT)
 if r.returncode:sys.exit(r.returncode)
