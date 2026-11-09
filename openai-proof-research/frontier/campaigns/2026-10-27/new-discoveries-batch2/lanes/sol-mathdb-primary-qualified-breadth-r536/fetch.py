import urllib.request,datetime,json,pathlib,hashlib
P=pathlib.Path(__file__).resolve().parent
out=[]
for aid in ['2606.19742','2606.25168','2607.21037','2607.11648','2606.12880','2606.11178','2605.03825']:
 url='https://arxiv.org/html/'+aid+'v1';e={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as r:b=r.read();e['status']=r.status;e['final_url']=r.url
  name=aid+'v1.html';(P/name).write_bytes(b);e.update(path=name,size=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as x:e['error']=str(x)
 out.append(e)
(P/'download-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
