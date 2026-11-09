from pathlib import Path
import shutil,subprocess,json
L=Path(__file__).resolve().parent;B=L.parent/'bench';W=B/'work'
for m in ['FamilyTree']+json.loads((L/'modules.json').read_text()):
 src=L.parent/'formal/FamilyTree.lean' if m=='FamilyTree' else L/(m+'.lean')
 shutil.copyfile(src,W/(m+'.lean'))
 q=subprocess.run(['python3',str(B/'run.py'),'-o',m+'.olean',m+'.lean'],cwd=W,capture_output=True,text=True)
 (L/(m+'.log')).write_text(q.stdout+q.stderr);print(m,q.returncode,flush=True)
 if q.returncode:break
