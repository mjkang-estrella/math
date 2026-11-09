import urllib.request,pathlib,json,hashlib,datetime,html.parser
L=pathlib.Path(__file__).resolve().parent
class Links(html.parser.HTMLParser):
 def handle_starttag(self,t,a):
  d=dict(a)
  if t=='a' and any(x in d.get('href','').lower() for x in ['pdf','arxiv']):print(d['href'])
out=[]
for id,url in [(404190,'https://ems.press/journals/owr/articles/14297743'),(404218,'https://ems.press/journals/owr/articles/14297736'),(404497,'https://ems.press/journals/owr/articles/14298371')]:
 r={'id':id,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'headers':'User-Agent: Python-urllib/3'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Python-urllib/3'}),timeout=25) as f:b=f.read(5000000);r['final_url']=f.url;r['status']=f.status
  p=L/(str(id)+'.html');p.write_bytes(b);r.update(path=p.name,size=len(b),sha256=hashlib.sha256(b).hexdigest());out.append(r)
  (L/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
  print(id);Links().feed(b.decode())
 except Exception as e:r['failure']=str(e);out.append(r);print(id,str(e))
 (L/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
