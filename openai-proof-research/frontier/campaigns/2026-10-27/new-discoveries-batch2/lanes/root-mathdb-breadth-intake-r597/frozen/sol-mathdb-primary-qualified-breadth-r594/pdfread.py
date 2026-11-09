import pathlib,json,re,hashlib,urllib.request,subprocess,datetime
P=pathlib.Path(__file__).resolve().parent;refs=json.loads((P/'flat-bindings.json').read_text());pro=json.loads((P/'source-provenance.json').read_text())
def bind(f):
 b=f.read_bytes();e={'path':str(f),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()};refs.append(e);(P/'flat-bindings.json').write_text(json.dumps(refs,indent=2)+'\n');return e
for id in ['11695867','14298801']:
 html=(P/(id+'.html')).read_text();urls=set(re.findall(r'https://content\.ems\.press/[^\s"<>\\]*\.pdf',html));assert len(urls)==1,urls
 url=urls.pop()
 try:
  b=urllib.request.urlopen(url,timeout=25).read();assert b.startswith(b'%PDF');f=P/(id+'.pdf');f.write_bytes(b);e=bind(f)
  t=P/(id+'-body.txt');subprocess.run(['pdftotext','-layout',str(f),str(t)],check=True);te=bind(t)
  pro.append({'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'raw':e,'derivative':te,'coverage':'Selected passages only; whole PDF extracted, not whole body read'})
 except Exception as e:pro.append({'url':url,'failure':str(e),'retry':False})
(P/'source-provenance.json').write_text(json.dumps(pro,indent=2)+'\n');print(json.dumps(pro[2:],indent=2))
