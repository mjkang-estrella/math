import urllib.request,urllib.error,json,pathlib,hashlib,datetime,html.parser
O=pathlib.Path(__file__).resolve().parent
log=json.loads((O/'source-provenance.json').read_text()) if (O/'source-provenance.json').exists() else []
class Links(html.parser.HTMLParser):
 def handle_starttag(self,tag,a):
  d=dict(a)
  if tag=='a' and ('pdf' in d.get('href','').lower() or 'serial-article-files' in d.get('href','')):print(d.get('href'))
for name,url in [('permutations','https://ems.press/journals/owr/articles/14298158'),('cayley','https://ems.press/journals/owr/articles/14299525'),('designs','https://ems.press/journals/owr/articles/14299518')]:
 p=O/(name+'.html')
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Python-urllib/3'}),timeout=25) as r:b=r.read(4000000);final=r.url;status=r.status
  p.write_bytes(b);e={'path':p.name,'url':url,'final_url':final,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'status':status};log.append(e)
  (O/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
  print(name,e);Links().feed(b.decode())
 except Exception as ex:
  log.append({'url':url,'failure':str(ex),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()});print(log[-1]);(O/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
