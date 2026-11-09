import urllib.request,datetime,re
urls=[('target-v1','https://arxiv.org/html/2502.04736v1'),('calligraph-v1','https://arxiv.org/html/2308.15305v1'),('definitions-v2','https://arxiv.org/html/2309.16416v2'),('definitions-v1','https://arxiv.org/html/2309.16416v1'),('alco-journal','https://alco.centre-mersenne.org/articles/10.5802/alco.390/'),('registry-vilin-projects','https://raw.githubusercontent.com/Vilin97/lean-pool/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/projects.yml'),('registry-openai-readme','https://raw.githubusercontent.com/openai/math/4eaee87548250b2682affda7d05d947c05554bae/README.md')]
receipts=json.loads((p/'http-receipts.json').read_text())
for name,url in urls:
 rec=dict(name=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(url,timeout=12) as q:
   data=q.read(5000000);rec.update(status=q.status,final_url=q.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest());(p/(name+'.html')).write_bytes(data)
  print(rec)
  t=data.decode();print('MATCHES',[(m.start(),t[max(0,m.start()-80):m.start()+250]) for m in re.finditer(r'367009|spherical|E1a|Calligraph|errat|corrig',t,re.I)][:12])
 except Exception as e:rec['error']=str(e);print(rec)
 receipts.append(rec)
(p/'http-receipts.json').write_text(json.dumps(receipts,indent=2))
