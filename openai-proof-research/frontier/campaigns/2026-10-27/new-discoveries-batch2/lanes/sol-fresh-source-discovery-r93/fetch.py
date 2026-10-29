import urllib.request,json,hashlib,datetime,pathlib,subprocess
P=pathlib.Path(__file__).parent; S=P/'sources'; records=[]
urls={
'vatter.pdf':'https://arxiv.org/pdf/2602.16355',
'vatter-abs.html':'https://arxiv.org/abs/2602.16355',
'kafidov.pdf':'https://arxiv.org/pdf/2607.20595',
'forest.pdf':'https://escholarship.org/content/qt9dc0v7wb/qt9dc0v7wb_noSplash_28ede5a36d36f74b24d311c99b18bfbc.pdf',
'chen.html':'https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7385218',
'omega-head.json':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD',
'openai-head.json':'https://api.github.com/repos/openai/math/commits/HEAD'}
for name,url in urls.items():
 r={'url':url,'file':'sources/'+name,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-check/1.0'}),timeout=35) as f:b=f.read(12000000);r.update(status=f.status,final_url=f.url)
  (S/name).write_bytes(b);r.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  if b.startswith(b'%PDF'): subprocess.run(['pdftotext','-layout',str(S/name),str(S/name.replace('.pdf','.txt'))],check=True)
 except Exception as e:r['error']=str(e)
 records.append(r)
(P/'http.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps(records,indent=2))
