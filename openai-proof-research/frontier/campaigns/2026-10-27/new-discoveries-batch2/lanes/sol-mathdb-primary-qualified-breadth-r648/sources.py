import pathlib,json,hashlib,urllib.request,datetime
from html.parser import HTMLParser
P=pathlib.Path(__file__).resolve().parent
log=[]
class Links(HTMLParser):
 def handle_starttag(self,t,a):
  d=dict(a)
  if t=='a' and 'href' in d and ('pdf' in d['href'] or 'download' in d['href']):print(d['href'])
for id in [3388,2053,2091]:
 u=f'https://ems.press/journals/owr/articles/{id}';p=P/f'ems{id}.html'
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Python-urllib/3'}),timeout=25) as r:b=r.read();final=r.url
  p.write_bytes(b);d={'url':u,'final_url':final,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':p.name,'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'kind':'primary landing HTML'};log.append(d)
  (P/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
  print('BOUND',id,d['sha256']);Links().feed(b.decode())
 except Exception as e:log.append({'url':u,'error':str(e),'stopped':True});(P/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n');print(e)
