import pathlib,urllib.request,hashlib,json,datetime,subprocess
O=pathlib.Path(__file__).resolve().parent;out=json.loads((O/'source-provenance.json').read_text());der=[]
for a,b in [('13853','46579'),('14219','46616'),('13490','46551')]:
 url='https://ems.press/content/serial-article-files/'+b+'?nt=1'
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Python-urllib/3'}),timeout=30) as r:d=r.read();final=r.url
  p=O/('ems'+a+'.pdf');p.write_bytes(d);x=dict(path=str(p),url=url,final_url=final,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),sha256=hashlib.sha256(d).hexdigest(),size=len(d));out.append(x)
  (O/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
  assert d.startswith(b'%PDF')
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
  t=p.with_suffix('.txt');v=t.read_bytes();der.append(dict(path=str(t),sha256=hashlib.sha256(v).hexdigest(),size=len(v),parent_sha256=x['sha256'],operation='pdftotext -layout'))
 except Exception as e:out.append(dict(url=url,error=str(e),stopped=True))
(O/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');(O/'derivative-bindings.json').write_text(json.dumps(der,indent=2)+'\n');print('bound',len(der),'text derivatives')
