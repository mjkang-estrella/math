import urllib.request,urllib.parse,pathlib,datetime,json,hashlib,xml.etree.ElementTree as E
L=pathlib.Path(__file__).parent;P=L/'prior';P.mkdir(exist_ok=True)
queries=[('arxiv-isometries','https://export.arxiv.org/api/query?'+urllib.parse.urlencode(dict(search_query='all:reconstruction AND (all:hypercube OR (all:Hamming AND all:isometries))',max_results=10))),('crossref-points','https://api.crossref.org/works?'+urllib.parse.urlencode({'query.bibliographic':'pseudosimilar points sets codes','rows':6,'select':'title,DOI,link,URL,published'}))]
for name,url in queries:
 r={'url':url,'utc':str(datetime.datetime.now(datetime.timezone.utc))}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical-source-review/1.0'}),timeout=35) as f:
   r.update(status=f.status,final_url=f.url,headers=dict(f.headers));data=f.read(2000001);assert len(data)<=2000000
  p=P/(name+'.body');p.write_bytes(data);r.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
  if name.startswith('arxiv'):
   tree=E.fromstring(data);ns={'a':'http://www.w3.org/2005/Atom'}
   print(name,[(e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns)) for e in tree.findall('a:entry',ns)])
  else: print(name,json.loads(data)['message']['items'])
 except Exception as e:r['error']=repr(e);print(name,r)
 (P/(name+'.receipt.json')).write_text(json.dumps(r,indent=2))
