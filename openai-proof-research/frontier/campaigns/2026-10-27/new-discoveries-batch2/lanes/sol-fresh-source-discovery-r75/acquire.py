import urllib.request,hashlib,json,datetime,pathlib
p=pathlib.Path(__file__).resolve().parent/'source-evidence'
urls={
'original.pdf':'https://sigma-journal.com/2020/076/sigma20-076.pdf',
'small.pdf':'https://arxiv.org/pdf/2605.12822v1',
'small-abs.html':'https://arxiv.org/abs/2605.12822',
'goswami.pdf':'https://arxiv.org/pdf/2603.04572v1',
'han-ren.pdf':'https://arxiv.org/pdf/2610.14496v1',
'registry-library.md':'https://raw.githubusercontent.com/the-omega-institute/trureturing/70af54071bfd4ac098619a9db8c16bb6f7aced11/Library/notes/connelly2026qfibonomial.md',
'registry-qproduct.md':'https://raw.githubusercontent.com/the-omega-institute/trureturing/70af54071bfd4ac098619a9db8c16bb6f7aced11/Blueprint/D5/S0/Certificates/Polynomials/QProductNecessityRefutation.md',
'registry-qproduct.lean':'https://raw.githubusercontent.com/the-omega-institute/trureturing/70af54071bfd4ac098619a9db8c16bb6f7aced11/D5/S0/Certificates/Polynomials/QProductNecessityRefutation.lean'}
rows=[]
for name,url in urls.items():
 row={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=30) as r:
   b=r.read();row.update(status=r.status,headers=dict(r.headers))
  if any(x in b[:20000].lower() for x in [b'just a moment',b'captcha',b'security challenge']):
   row['error']='challenge: route stopped';(p/(name+'.challenge')).write_bytes(b)
  else:
   (p/name).write_bytes(b);row.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:row['error']=str(e)
 rows.append(row);print(name,row.get('status'),row.get('error','OK'),flush=True)
(p/'acquisition.json').write_text(json.dumps(rows,indent=2))
