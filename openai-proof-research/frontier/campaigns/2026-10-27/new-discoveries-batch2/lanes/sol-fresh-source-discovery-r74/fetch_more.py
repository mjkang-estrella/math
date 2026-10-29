import pathlib,json,urllib.request,datetime,hashlib,subprocess
L=pathlib.Path(__file__).resolve().parent
urls={
'renyi-arxiv.pdf':'https://arxiv.org/pdf/2005.10930',
'renyi-abs.html':'https://arxiv.org/abs/2005.10930',
'lyapunov-abs.html':'https://arxiv.org/abs/2111.06997',
'gram.html':'https://mathoverflow.net/questions/479107/more-on-the-gram-matrix-of-6-unit-vectors-in-bbb-r3',
'existence.html':'https://mathoverflow.net/questions/481234/does-there-exist-such-a-probability-distribution',
'registry-chernoff.md':'https://raw.githubusercontent.com/the-omega-institute/trureturing/6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3/Problems/salek-hayashi-winter-2020-harrow-parallel-chernoff-exponent.md',
'count-readme.md':'https://raw.githubusercontent.com/suvrit/count-ex-machina/dbf673741a54c7dc9d88a6aec0e8148a538f4a3a/README.md',
'openai-readme.md':'https://raw.githubusercontent.com/openai/math/main/README.md'
}
rows=[]
for name,url in urls.items():
 row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'sources/'+name}
 try:
  with urllib.request.urlopen(url,timeout=20) as r:body=r.read(12000000);row.update(status=r.status,headers=dict(r.headers))
  (L/row['file']).write_bytes(body);row.update(sha256=hashlib.sha256(body).hexdigest(),bytes=len(body))
  if body.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(L/row['file']),str(L/'sources'/name.replace('.pdf','.txt'))],check=True)
 except Exception as e:row['error']=str(e)
 rows.append(row);(L/'http-more.json').write_text(json.dumps(rows,indent=2))
print(json.dumps([{k:v for k,v in r.items() if k!='headers'} for r in rows]))
