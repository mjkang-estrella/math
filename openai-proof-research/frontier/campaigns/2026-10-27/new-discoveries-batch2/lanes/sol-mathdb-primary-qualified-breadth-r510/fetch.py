import pathlib,json,urllib.request,urllib.error,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent;(P/'sources').mkdir(exist_ok=True);out=[]
for a in ['2609.26324','2609.26762','2609.20385','2609.25552','2101.03428']:
 url='https://arxiv.org/html/'+a;rec={'requested_url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'version':'unversioned endpoint; inspect returned version metadata','body_read':False}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research-screen/1.0'}),timeout=25) as r:
   b=r.read(12000000);rec.update(status=r.status,final_url=r.url,headers=dict(r.headers))
  p=P/'sources'/ (a+'.html');p.write_bytes(b);rec.update(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:rec['error']=str(e)
 out.append(rec);print(a,rec.get('status'),rec.get('size'),rec.get('error'))
(P/'source-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
