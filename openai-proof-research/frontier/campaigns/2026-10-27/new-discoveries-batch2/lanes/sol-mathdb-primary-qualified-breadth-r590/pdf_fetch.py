import pathlib,urllib.request,json,hashlib,datetime,re,subprocess
P=pathlib.Path(__file__).resolve().parent;out=[];fails=[]
for id in ['12861','14741','12975','12872','12983']:
 b=(P/('ems-'+id+'.html')).read_bytes()
 e=next(x for x in json.loads((P/'source-provenance.json').read_text()) if x['path']=='ems-'+id+'.html')
 assert hashlib.sha256(b).hexdigest()==e['sha256']
 url=re.search(r'https://ems.press/content/serial-article-files/[0-9]+',b.decode()).group()
 try:
  utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
  with urllib.request.urlopen(url,timeout=25) as r:b=r.read()
  assert b.startswith(b'%PDF')
  p=P/('ems-'+id+'.pdf');p.write_bytes(b);out.append(dict(path=p.name,url=url,utc=utc,size=len(b),sha256=hashlib.sha256(b).hexdigest()))
 except Exception as e:fails.append(dict(url=url,error=str(e)))
(P/'pdf-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
(P/'pdf-failures.json').write_text(json.dumps(fails,indent=2)+'\n')
der=[]
for e in out:
 p=P/e['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==e['sha256']
 t=p.with_suffix('.body.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True)
 b=t.read_bytes();der.append(dict(path=t.name,size=len(b),sha256=hashlib.sha256(b).hexdigest(),from_path=p.name))
(P/'pdf-derivative-bindings.json').write_text(json.dumps(der,indent=2)+'\n')
print(json.dumps(out+fails,indent=2))
