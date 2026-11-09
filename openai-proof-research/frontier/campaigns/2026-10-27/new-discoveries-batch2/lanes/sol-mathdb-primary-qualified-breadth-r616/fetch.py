import pathlib,hashlib,json,urllib.request,datetime
P=pathlib.Path(__file__).parent;out=[]
for aid in ['2607.08366','2602.14741','2607.00988','2601.13779']:
 u='https://arxiv.org/html/'+aid+'v1';e={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'headers':{'User-Agent':'Mozilla/5.0','Accept':'text/html'}}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers=e['headers']),timeout=25) as r:b=r.read();e.update(status=r.status,final_url=r.url)
  f=P/(aid+'.html');f.write_bytes(b);e.update(path=str(f),size=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as ex:e['failure']=str(ex)
 out.append(e)
(P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
