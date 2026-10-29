from pathlib import Path
import urllib.request,hashlib,json,datetime,subprocess
P=Path(__file__).resolve().parent;S=P/'sources';log=[]
urls={'GM-v3.pdf':'https://arxiv.org/pdf/2308.15997v3','BNT-latest.pdf':'https://arxiv.org/pdf/1509.05926','Bobkov-published.pdf':'https://www-users.cse.umn.edu/~bobko001/papers/2022_EJP_Upper.bounds.for.Fisher.information.pdf','omega-CDSO.md':'https://raw.githubusercontent.com/the-omega-institute/trureturing/73a5033dd654a16a14fcd1b13277f1a03d81d826/docs/develop/theory/CDSO_INCIDENCE_MOMENTS_AND_CAPACITY_PHASES.md'}
for name,url in urls.items():
 row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  r=urllib.request.urlopen(url,timeout=20);b=r.read(12000000);(S/name).write_bytes(b);row.update(file='sources/'+name,status=r.status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  if name.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(S/name),str(S/(name+'.txt'))],check=True)
 except Exception as e:row['error']=str(e)
 log.append(row);print(name,row.get('status',row.get('error')),flush=True)
(P/'more-http.json').write_text(json.dumps(log,indent=2))
