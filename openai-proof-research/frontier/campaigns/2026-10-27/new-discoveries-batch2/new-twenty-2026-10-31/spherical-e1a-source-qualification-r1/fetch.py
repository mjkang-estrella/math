import urllib.request,datetime,re
urls=[('registry-openai','https://github.com/openai/math'),('registry-vilin','https://github.com/Vilin97/lean-pool'),('target-abs','https://arxiv.org/abs/2502.04736'),('calligraph-abs','https://arxiv.org/abs/2308.15305'),('definitions-abs','https://arxiv.org/abs/2309.16416')]
receipts=[]
for name,url in urls:
 rec=dict(name=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(url,timeout=15) as q:
   data=q.read(5000000);rec.update(status=q.status,final_url=q.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest());(p/(name+'.html')).write_bytes(data)
  t=data.decode();print(name,rec);print('HEADS',re.findall(r'"currentOid":"([0-9a-f]{40})"',t));print('VERSIONS',re.findall(r'(?s)Submission history.{0,4500}',t)[:1]);print('JOURNAL',re.findall(r'(?s)(?:Journal reference|journal-ref|doi.org).{0,500}',t)[:4])
 except Exception as e:rec['error']=str(e);print(rec)
 receipts.append(rec)
(p/'http-receipts.json').write_text(json.dumps(receipts,indent=2))
