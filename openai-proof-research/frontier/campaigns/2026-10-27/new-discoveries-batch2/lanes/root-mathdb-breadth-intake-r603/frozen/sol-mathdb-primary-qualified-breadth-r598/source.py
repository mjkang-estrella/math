import pathlib,urllib.request,hashlib,json,datetime
P=pathlib.Path(__file__).resolve().parent;out=[]
for a in ['1106.2355','1306.0431','1301.6983']:
 u='https://arxiv.org/html/'+a+'v1';r={'url':u,'version':'v1','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=35) as f:b=f.read();r['status']=f.status;r['final_url']=f.url
  p=P/(a+'.html');p.write_bytes(b);r.update(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:r['failure']=str(e)
 out.append(r)
(P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
