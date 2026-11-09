import pathlib,urllib.request,hashlib,json,datetime
O=pathlib.Path(__file__).resolve().parent
out=[]
for a in ['13853','14219','13490']:
 url='https://ems.press/journals/owr/articles/'+a
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Python-urllib/3'}),timeout=25) as r: data=r.read(); final=r.url
  p=O/('ems'+a+'.html');p.write_bytes(data);out.append(dict(path=str(p),url=url,final_url=final,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),sha256=hashlib.sha256(data).hexdigest(),size=len(data)))
 except Exception as e:out.append(dict(url=url,error=str(e),stopped=True))
(O/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
