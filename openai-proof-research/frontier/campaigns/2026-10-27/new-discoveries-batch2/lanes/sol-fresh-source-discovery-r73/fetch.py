import urllib.request,json,hashlib,datetime,pathlib
r=pathlib.Path(__file__).resolve().parent
urls={'sun-oeis.html':'https://oeis.org/A390107/internal','he-yuan.pdf':'https://ssmr.ro/bulletin/pdf/67-4/articol_4.pdf','amiri.html':'https://arxiv.org/html/2511.08320v2','amiri-abs.html':'https://arxiv.org/abs/2511.08320','omega-readme.md':'https://raw.githubusercontent.com/teorth/ai-math/refs/heads/main/README.md'}
rows=[]
for name,url in urls.items():
 d={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'sources/'+name}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:v=f.read(12000000);d.update(status=f.status,final_url=f.url)
  (r/d['file']).write_bytes(v);d['sha256']=hashlib.sha256(v).hexdigest()
 except Exception as e:d['error']=repr(e)
 rows.append(d)
(r/'sources/fetch.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
