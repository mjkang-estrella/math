import pathlib,json,re,urllib.request,hashlib,datetime,subprocess
O=pathlib.Path(__file__).resolve().parent;pro=json.loads((O/'source-provenance.json').read_text());der=json.loads((O/'derivative-bindings.json').read_text());fails=json.loads((O/'fetch-failures.json').read_text())
for name in ['rectangle','invariants','approximation','inversion']:
 s=(O/(name+'.txt')).read_text();urls=re.findall(r'https://content\.ems\.press/[^"\\\s]+\.pdf',s);assert urls,name
 url=urls[0]
 try:
  with urllib.request.urlopen(url,timeout=25) as f:b=f.read();final=f.url
  p=O/(name+'.pdf');p.write_bytes(b);pro.append(dict(path=str(p),url=url,final_url=final,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),size=len(b),sha256=hashlib.sha256(b).hexdigest(),version='EMS published report'))
  (O/'source-provenance.json').write_text(json.dumps(pro,indent=2)+'\n')
  q=O/(name+'-body.txt');subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True);der.append(dict(path=str(q),size=q.stat().st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest(),parent=str(p)))
  (O/'derivative-bindings.json').write_text(json.dumps(der,indent=2)+'\n')
 except Exception as e:fails.append(dict(url=url,error=str(e)))
(O/'fetch-failures.json').write_text(json.dumps(fails,indent=2)+'\n');print('PDF bindings',len(pro),'failures',fails)
