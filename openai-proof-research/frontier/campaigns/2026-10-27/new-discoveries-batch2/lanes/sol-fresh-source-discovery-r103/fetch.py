from pathlib import Path
import urllib.request,json,hashlib,datetime,subprocess
P=Path(__file__).resolve().parent;S=P/'sources';log=[]
urls={'omega-head.json':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD','openai-head.json':'https://api.github.com/repos/openai/math/commits/HEAD','BNT-abs.html':'https://arxiv.org/abs/1509.05926','BNT.pdf':'https://www.mimuw.edu.pl/~nayar/revent1.pdf','GM-published.pdf':'https://api.repository.cam.ac.uk/server/api/core/bitstreams/65fadfa1-b3a9-4829-83b3-6bac70291d9b/content','Feige-v2.pdf':'https://people.clas.ufl.edu/amarsiglietti/files/2208.12702v2.pdf'}
for name,url in urls.items():
 row={'file':'sources/'+name,'url':url,'time':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  r=urllib.request.urlopen(url,timeout=20);b=r.read(16000000);(S/name).write_bytes(b);row.update(status=r.status,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());print(name,len(b),flush=True)
  if name.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(S/name),str(S/(name+'.txt'))],check=True)
 except Exception as e:row['error']=str(e);print(name,e,flush=True)
 log.append(row);(P/'http.json').write_text(json.dumps(log,indent=2))
