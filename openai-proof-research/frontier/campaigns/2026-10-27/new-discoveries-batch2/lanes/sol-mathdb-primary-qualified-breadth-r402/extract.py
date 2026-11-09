from pathlib import Path
import subprocess,json,hashlib,datetime
O=Path(__file__).resolve().parent/'primary'; report=[]
for p in sorted(O.glob('*.pdf')):
 m=json.loads(p.with_suffix('.meta.json').read_text()); assert hashlib.sha256(p.read_bytes()).hexdigest()==m['sha256']
 t=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True)
 report.append({'input':str(p),'output':str(t),'sha256':hashlib.sha256(t.read_bytes()).hexdigest(),'size':t.stat().st_size,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
(O/'extractions.json').write_text(json.dumps(report,indent=2)+'\n')
