from pathlib import Path
import shutil,subprocess
L=Path(__file__).resolve().parent;B=L.parent/'bench';W=B/'work'
for size in [7,8,9,10]:
 for count in [8,32,128]:
  m='Local%dN%d'%(size,count)
  shutil.copyfile(L/(m+'.lean'),W/(m+'.lean'))
  q=subprocess.run(['python3',str(B/'run.py'),'-o',m+'.olean',m+'.lean'],cwd=W,capture_output=True,text=True)
  (L/(m+'.log')).write_text(q.stdout+q.stderr);print(m,q.returncode,flush=True)
