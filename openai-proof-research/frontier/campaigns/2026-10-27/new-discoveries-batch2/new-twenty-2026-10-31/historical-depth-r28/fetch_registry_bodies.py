import pathlib,json,urllib.request,urllib.parse,datetime,hashlib
D=pathlib.Path(__file__).resolve().parent; data=json.loads((D/'registry-screen.json').read_text()); items={f'registry-freebycyclic-{i}':'https://raw.githubusercontent.com/openai/math/'+data['live_head']+'/preprints/'+urllib.parse.quote(path) for i,path in enumerate(data['hits']['free-by-cyclic'])};items['unsolvedmath-list']='https://www.unsolvedmath.com/problems?category=17&difficulty=3&status=partially_solved'
for name,url in items.items():
 rec=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(url,timeout=20) as r:
   raw=r.read(5000000);rec.update(status=r.status,sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),final_url=r.url);(D/'sources'/(name+'.body')).write_bytes(raw)
 except Exception as e:rec['error']=str(e)
 (D/'sources'/(name+'.receipt.json')).write_text(json.dumps(rec,indent=2)+'\n');print(name,rec.get('status'),rec.get('error',''))
