import pathlib,urllib.request,urllib.error,datetime,json,hashlib
L=pathlib.Path(__file__).resolve().parent;(L/'evidence').mkdir(exist_ok=True)
urls={
'egres':'https://oldlemon.cs.elte.hu/egres/open/List_of_open_problems',
'cooper':'https://people.math.sc.edu/cooper/combprob.html',
'eremenko':'https://www.math.purdue.edu/~eremenko/uns1.html',
'jeffe':'https://jeffe.cs.illinois.edu/open/',
'comb':'https://jeffe.cs.illinois.edu/open/comb.html',
'intricate':'https://jeffe.cs.illinois.edu/open/intricate.html',
'tangents':'https://jeffe.cs.illinois.edu/open/tangents.html',
'algo':'https://jeffe.cs.illinois.edu/open/algo.html',
'goldconst':'https://www.math.purdue.edu/~eremenko/dvi/goldconst.pdf',
'quadr':'https://www.math.purdue.edu/~eremenko/dvi/quadr.pdf',
'hypercut':'https://par.nsf.gov/servlets/purl/10174429',
'preference':'https://arxiv.org/html/2409.16173'}
log=[]
for name,url in urls.items():
 e={'name':name,'requested_url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-check/1.0'}),timeout=18) as f:
   b=f.read(6000000);e.update(status=f.status,final_url=f.url,headers=dict(f.headers));assert len(b)<6000000
  p=L/'evidence'/(name+('.pdf' if b.startswith(b'%PDF') else '.html'));p.write_bytes(b)
  e.update(path=str(p.relative_to(L)),sha256=hashlib.sha256(b).hexdigest(),size=len(b),version='response body retained; Last-Modified/ETag in headers where supplied')
 except Exception as ex:e['failure']=str(ex)
 log.append(e);(L/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n');print(name,e.get('status'),e.get('failure'),e.get('size'),flush=True)
