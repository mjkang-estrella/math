from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent
for name in ['scientific-freeze.json','finalmanifest.json']:
 j=json.loads((L/name).read_bytes())
 for p,h in j['files'].items():assert hashlib.sha256((L/p).read_bytes()).hexdigest()==h,(name,p)
 print(name,'PASS',len(j['files']))
