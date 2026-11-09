import pathlib,urllib.request,hashlib,json,datetime
D=pathlib.Path(__file__).resolve().parent;out=[]
for aid in ['2507.14244','2508.00111','2509.10232','2510.11753','2510.09265','2509.01901']:
 url='https://arxiv.org/html/'+aid+'v1';t=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(url,timeout=25) as r:b=r.read();status=r.status;final=r.url
  p=D/(aid+'v1.html');p.write_bytes(b)
  out.append(dict(url=url,final_url=final,utc=t,status=status,path=p.name,size=len(b),sha256=hashlib.sha256(b).hexdigest(),version='v1',body_read=False))
 except Exception as e:
  out.append(dict(url=url,utc=t,error=str(e),body_read=False))
  if any(s in str(e) for s in ['403','429']):break
(D/'retrieval-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
