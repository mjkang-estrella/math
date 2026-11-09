import urllib.request,pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent
out=[]
for n in [784,787,793,742,828]:
 url=f'https://ems.press/journals/owr/articles/{n}'
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0','Accept':'text/html'}),timeout=25) as r:b=r.read();final=r.url
  p=P/f'ems{n}.html';p.write_bytes(b);out.append(dict(url=url,final_url=final,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),path=p.name,size=len(b),sha256=hashlib.sha256(b).hexdigest()))
 except Exception as e:out.append(dict(url=url,error=str(e),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
(P/'fetch-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
