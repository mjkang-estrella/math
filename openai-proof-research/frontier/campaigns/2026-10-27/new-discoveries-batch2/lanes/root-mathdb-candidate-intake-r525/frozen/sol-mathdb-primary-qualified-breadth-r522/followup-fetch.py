import urllib.request,hashlib,json,datetime,pathlib
P=pathlib.Path(__file__).resolve().parent;out=[]
for ar in ['2410.17057','2412.17391']:
 url='https://arxiv.org/abs/'+ar;e={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as r:b=r.read();e.update(status=r.status,final_url=r.url)
  p=P/(ar+'-history.html');p.write_bytes(b);e.update(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
 except Exception as ex:e.update(error=str(ex),retry=False)
 out.append(e);print(json.dumps(e))
(P/'version-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
