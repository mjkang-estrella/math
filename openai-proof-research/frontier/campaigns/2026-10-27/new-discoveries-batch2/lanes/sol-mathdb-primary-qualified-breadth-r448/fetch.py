import pathlib,json,urllib.request,urllib.error,hashlib,re
O=pathlib.Path(__file__).parent;(O/'sources').mkdir(exist_ok=True);out=[]
for n in ['17464','1703861','4990379','7155446','7155450','1703876']:
 url='https://ems.press/journals/owr/articles/'+n
 try:
  with urllib.request.urlopen(url,timeout=25) as f:data=f.read(4000000);status=f.status;final=f.url
  p=O/'sources'/(n+'.html');p.write_bytes(data)
  out.append(dict(url=url,final_url=final,status=status,path=str(p.relative_to(O)),size=len(data),sha256=hashlib.sha256(data).hexdigest()))
  links=re.findall(r'https[^"<>\s]+\.pdf[^"<>\s]*',data.decode())
  print(n,'pdf links',list(dict.fromkeys(links))[:8])
 except Exception as e:out.append(dict(url=url,error=str(e)));print(n,str(e))
(O/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
