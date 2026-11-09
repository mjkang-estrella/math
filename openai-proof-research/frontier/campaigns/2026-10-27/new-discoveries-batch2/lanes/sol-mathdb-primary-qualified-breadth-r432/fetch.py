import urllib.request,pathlib,json,re,hashlib,time
O=pathlib.Path(__file__).resolve().parent;S=O/'sources';S.mkdir(exist_ok=True);events=[]
for key in ['4539','4791','4798','4800','11129','11134','11136']:
 url='https://ems.press/journals/owr/articles/'+key
 try:
  with urllib.request.urlopen(url,timeout=20) as r:b=r.read();final=r.url
  (S/(key+'.html')).write_bytes(b);events.append({'url':url,'final_url':final,'file':'sources/'+key+'.html','sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'kind':'article landing page, not proof'})
  links=re.findall(r'(?:href|content)=["\']([^"\']+\.pdf[^"\']*)',b.decode())
  print(key,links[:5],flush=True)
  if not links:continue
  pdf=urllib.request.urljoin(url,links[0])
  with urllib.request.urlopen(pdf,timeout=20) as r:b=r.read();final=r.url
  assert b.startswith(b'%PDF')
  (S/(key+'.pdf')).write_bytes(b);events.append({'url':pdf,'final_url':final,'file':'sources/'+key+'.pdf','sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'kind':'primary report PDF downloaded; inspection separately recorded'})
 except Exception as e:
  events.append({'url':url,'failure':repr(e),'retry':False});print(repr(e),flush=True)
  if getattr(e,'code',None) in [403,429]:break
(O/'source-provenance.json').write_text(json.dumps(events,indent=2)+'\n')
