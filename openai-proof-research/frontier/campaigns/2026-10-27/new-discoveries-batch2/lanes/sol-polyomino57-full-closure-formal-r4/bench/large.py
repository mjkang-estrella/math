from pathlib import Path
import shutil,subprocess
L=Path(__file__).resolve().parent;W=L/'work'
for m in ['Layer9','Layer10','Layer11']:
 shutil.copyfile(L/'formal'/(m+'.lean'),W/(m+'.lean'))
 q=subprocess.run(['python3',str(L/'run.py'),'-o',m+'.olean',m+'.lean'],cwd=W,capture_output=True,text=True)
 (L/(m+'.log')).write_text(q.stdout+q.stderr);print(m,q.returncode,flush=True)
