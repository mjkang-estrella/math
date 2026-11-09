exec(open(__file__.replace('extra.py','fetch.py')).read().split('rows=list')[0])
items=[('hyperbolic-resolution','https://arxiv.org/pdf/2601.10602'),('efron-published','https://tropp.caltech.edu/papers/PMT16-Efron-Stein-Inequalities.pdf')]
rows=list(ThreadPoolExecutor(max_workers=2).map(fetch,items))
for name,url in [('openai','https://github.com/openai/math'),('omega','https://github.com/trureturing/omega-institute/tree/dev')]:
 r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=35) as f:data=f.read(6000000);r['status']=f.status
  (out/'sources'/f'{name}.html').write_bytes(data);r['sha256']=hashlib.sha256(data).hexdigest()
  import re
  r['currentOid']=sorted(set(re.findall(r'"currentOid":"([a-f0-9]{40})"',data.decode())))
 except Exception as e:r['error']=str(e)
 rows.append(r)
(out/'extra-receipts.json').write_text(json.dumps(rows,indent=2));print(rows)
