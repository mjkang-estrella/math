from retrieve import get,L,P
import subprocess,hashlib,json
rows=[]
for id in ['2510.25442v1','2402.13202v1']:
 r=get('https://arxiv.org/pdf/'+id,id+'.pdf')
 if 'failure' in r:continue
 p=P/(id+'.pdf');q=p.with_suffix('.txt');h=hashlib.sha256(p.read_bytes()).hexdigest()
 subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True);assert h==hashlib.sha256(p.read_bytes()).hexdigest()
 rows.append({'pdf':str(p),'sha256':h,'text':str(q),'text_sha256':hashlib.sha256(q.read_bytes()).hexdigest()})
 lines=q.read_text().splitlines();print(id,'\n'.join(lines[:125]))
(L/'last-bindings.json').write_text(json.dumps(rows,indent=2))
