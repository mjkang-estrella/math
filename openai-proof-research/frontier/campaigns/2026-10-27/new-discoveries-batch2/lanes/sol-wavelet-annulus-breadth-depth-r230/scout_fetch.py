from retrieve import get,L,P
import subprocess,hashlib,json
rows=[]
for id in ['2510.11908v2','2504.04845v1','2511.18217v1','2512.17285v1']:
 rec=get('https://arxiv.org/pdf/'+id,id+'.pdf')
 if 'failure' in rec:continue
 p=P/(id+'.pdf');q=p.with_suffix('.txt');before=hashlib.sha256(p.read_bytes()).hexdigest()
 subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==before
 rows.append({'pdf':str(p),'sha256':before,'text':str(q),'text_sha256':hashlib.sha256(q.read_bytes()).hexdigest()})
 print('TEXT',id)
 lines=q.read_text().splitlines()
 for i,s in enumerate(lines):
  if any(w in s for w in ['Question','Problem','Conjecture']): print(i,'\n'.join(lines[max(0,i-1):i+9]))
(L/'scout-text-bindings.json').write_text(json.dumps(rows,indent=2))
