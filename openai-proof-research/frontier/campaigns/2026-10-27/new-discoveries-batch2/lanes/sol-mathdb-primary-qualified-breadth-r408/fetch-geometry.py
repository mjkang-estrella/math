import pathlib,urllib.request,datetime,json,hashlib
L=pathlib.Path(__file__).resolve().parent
urls={'unfold':'https://jeffe.cs.illinois.edu/open/unfold.html','ksets':'https://jeffe.cs.illinois.edu/open/ksets.html','medialaxis':'https://jeffe.cs.illinois.edu/open/medialaxis.html','happyend':'https://jeffe.cs.illinois.edu/open/happyend.html'}
log=json.loads((L/'source-provenance.json').read_text())
for name,url in urls.items():
 e={'name':name,'requested_url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-check/1.0'}),timeout=18) as f:
   b=f.read(6000000);e.update(status=f.status,final_url=f.url,headers=dict(f.headers));assert len(b)<6000000
  p=L/'evidence'/(name+('.pdf' if b.startswith(b'%PDF') else '.html'));p.write_bytes(b);e.update(path=str(p.relative_to(L)),sha256=hashlib.sha256(b).hexdigest(),size=len(b),version='retained response; explicit version in URL when supplied')
 except Exception as ex:e['failure']=str(ex)
 log.append(e);(L/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n');print(name,e.get('status'),e.get('failure'),e.get('size'),flush=True)
