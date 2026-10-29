import urllib.request,datetime,hashlib,json,pathlib
p=pathlib.Path(__file__).parent/'live';p.mkdir(exist_ok=True)
urls={'arxiv-abs':'https://arxiv.org/abs/2511.14514','conference-program':'https://mozart.diei.unipg.it/walcom2026/Program.pdf','author-publications':'https://jbensmai.fr/'}
records=[]
for name,url in urls.items():
 r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:
   b=f.read(5000000);r.update(status=f.status,final_url=f.url,headers=dict(f.headers),bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(p/name).write_bytes(b)
 except Exception as e:r['error']=str(e)
 records.append(r)
(p/'http.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps(records,indent=2))
