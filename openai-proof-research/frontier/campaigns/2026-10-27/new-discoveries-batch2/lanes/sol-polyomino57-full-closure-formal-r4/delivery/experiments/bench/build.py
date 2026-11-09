from pathlib import Path
import json,shutil,subprocess
L=Path(__file__).resolve().parent;W=L/'work';W.mkdir(exist_ok=True)
# All dependencies were freshly replayed from immutable archive in this lane.
for p in (L.parent/'closure/work').glob('*.olean'):shutil.copyfile(p,W/p.name)
for m in ['Layer8','Closure7C000','Closure7C047','Closure7C094']:
 shutil.copyfile(L/'formal'/(m+'.lean'),W/(m+'.lean'))
 q=subprocess.run(['python3',str(L/'run.py'),'-o',m+'.olean',m+'.lean'],cwd=W,capture_output=True,text=True)
 (L/(m+'.log')).write_text(q.stdout+q.stderr);print(m,q.returncode,flush=True)
 if q.returncode:break
