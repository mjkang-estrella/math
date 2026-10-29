from pathlib import Path
import hashlib,json,subprocess,shutil,sys,time,re
L=Path(__file__).resolve().parent
mods=['Grid','Growth','Normalization','Bounds','Witness','Efficient','Coverage','Existence','ListCertificate','Assembly','SortedCertificate','PlacementTree','LocalAssembly']+json.loads((L/'generated-modules.json').read_text())
W=L/'work';W.mkdir(exist_ok=True);V=L/'verification';V.mkdir(exist_ok=True)
for m in mods:shutil.copyfile(L/'formal'/(m+'.lean'),W/(m+'.lean'))
for m in mods:
 if (W/(m+'.olean')).exists() and '--fresh' not in sys.argv:continue
 q=subprocess.run(['python3',str(L/'run.py'),'-o',m+'.olean',m+'.lean'],cwd=W,capture_output=True,text=True)
 (V/(m+'.log')).write_text(q.stdout+q.stderr)
 print(m,q.returncode,flush=True)
 if q.returncode:sys.exit(q.returncode)
 assert not q.stdout and not q.stderr
