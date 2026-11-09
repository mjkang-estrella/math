import subprocess,sys,uuid
from pathlib import Path
lane=Path(__file__).resolve().parent.parent
m=sys.argv[1]; log=lane/'logs'/(uuid.uuid4().hex[:12]+'-'+m+'.log')
with log.open('w') as f:
 rc=subprocess.run([str(lane/'scripts/lean.sh'),'--root=src','-o',str(lane/'build'/(m+'.olean')),'src/'+m+'.lean'],cwd=lane,stdout=f,stderr=subprocess.STDOUT).returncode
print(log.name, rc); print(log.read_text()[-9000:]);sys.exit(rc)
