import urllib.request,pathlib,hashlib,json,datetime
L=pathlib.Path(__file__).resolve().parent;out=[]
for name,url in [('target-v1.pdf','https://arxiv.org/pdf/2610.17046v1'),('companion-abs.html','https://arxiv.org/abs/2610.13366')]:
 row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as r:data=r.read(2000000);row['status']=r.status
  p=L/'live'/name;p.write_bytes(data);p.chmod(0o444);row.update(path=str(p),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
 except Exception as e:row['failure']=repr(e)
 out.append(row)
(L/'refresh-access.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
