import pathlib,urllib.request,datetime,json,hashlib
L=pathlib.Path(__file__).resolve().parent
urls={'gross':'https://www.math.purdue.edu/~eremenko/dvi/gross.pdf','gpolep':'https://www.math.purdue.edu/~eremenko/dvi/gpolep.pdf','erd':'https://www.math.purdue.edu/~eremenko/dvi/erd.pdf','nadi':'https://arxiv.org/html/2609.29797v1','gabrielov':'https://arxiv.org/html/2008.07999','tao':'https://arxiv.org/html/2512.12455','control2':'https://www.math.purdue.edu/~eremenko/dvi/control2.pdf'}
log=json.loads((L/'source-provenance.json').read_text())
for name,url in urls.items():
 e={'name':name,'requested_url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-check/1.0'}),timeout=18) as f:
   b=f.read(6000000);e.update(status=f.status,final_url=f.url,headers=dict(f.headers));assert len(b)<6000000
  p=L/'evidence'/(name+('.pdf' if b.startswith(b'%PDF') else '.html'));p.write_bytes(b);e.update(path=str(p.relative_to(L)),sha256=hashlib.sha256(b).hexdigest(),size=len(b),version='retained response; explicit version in URL when supplied')
 except Exception as ex:e['failure']=str(ex)
 log.append(e);(L/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n');print(name,e.get('status'),e.get('failure'),e.get('size'),flush=True)
