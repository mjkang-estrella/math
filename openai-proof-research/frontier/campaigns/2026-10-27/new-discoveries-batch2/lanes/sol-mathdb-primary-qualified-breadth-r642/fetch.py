import urllib.request,urllib.error,pathlib,json,hashlib,datetime,re,subprocess
P=pathlib.Path(__file__).resolve().parent
log=[];bindings=[]
def bind(p):
 b=p.read_bytes();e={'path':str(p.resolve()),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()};bindings.append(e);(P/'download-bindings.json').write_text(json.dumps(bindings,indent=2)+'\n')
def fetch(url,name):
 e={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'ResearchReader/1.0','Accept':'*/*'}),timeout=25) as r:
   b=r.read(10000000);e.update(status=r.status,final_url=r.url)
  p=P/name;p.write_bytes(b);bind(p);e.update(sha256=hashlib.sha256(b).hexdigest(),size=len(b));log.append(e);return p
 except Exception as ex:e['error']=str(ex);log.append(e);return None
 finally:(P/'fetch-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
for id in ['1190','1274','1386','1452','1453','1394']:
 p=fetch('https://ems.press/journals/owr/articles/'+id,'ems'+id+'.html')
 if not p:continue
 s=p.read_text();links=re.findall(r'(?:href|content)="([^"]+\.pdf[^" ]*)"',s)
 print(id,links[:4])
 if links:
  url=urllib.parse.urljoin('https://ems.press',links[0]);q=fetch(url,'ems'+id+'.pdf')
  if q:
   subprocess.run(['pdftotext','-layout',str(q),str(P/('ems'+id+'.txt'))],check=True);bind(P/('ems'+id+'.txt'))
