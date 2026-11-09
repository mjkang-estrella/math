import urllib.request,urllib.parse,pathlib,hashlib,json,datetime,sys
L=pathlib.Path(__file__).resolve().parent
urls=[('arxiv-abs','https://arxiv.org/abs/2307.00545'),('crossref','https://api.crossref.org/works?query.title='+urllib.parse.quote('Properties and conjectures regarding discrete renewal sequences')+'&rows=3')]
if len(sys.argv)>2: urls=[(sys.argv[1],sys.argv[2])]
records=json.loads((L/'access.json').read_text()) if (L/'access.json').exists() else []
for name,url in urls:
 assert not any(t['url']==url for t in records),'no repeat retrieval'
 r=dict(name=name,url=url,time=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical-source-review/1.0'}),timeout=25) as f:
   b=f.read(2000000);r.update(status=f.status,final_url=f.url,bytes=len(b))
  p=L/'retrieved'/f'{name}.body';p.parent.mkdir(exist_ok=True);p.write_bytes(b)
  q=L/'retrieved'/f'{name}.frozen';q.write_bytes(b)
  r.update(original=str(p.relative_to(L)),copy=str(q.relative_to(L)),sha256=hashlib.sha256(b).hexdigest());assert p.read_bytes()==q.read_bytes()
 except Exception as e:r['failure']=str(e)
 records.append(r)
(L/'access.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps(records))
