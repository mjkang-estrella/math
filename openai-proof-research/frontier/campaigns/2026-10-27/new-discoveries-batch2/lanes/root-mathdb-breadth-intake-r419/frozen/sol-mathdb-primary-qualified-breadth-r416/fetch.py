import pathlib,json,urllib.request,urllib.error,datetime,hashlib,sys
L=pathlib.Path(__file__).parent;E=L/'evidence';E.mkdir(exist_ok=True)
name,url=sys.argv[1:];p=E/(name+'.body');meta={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'version':'server response at retrieval time; no publication equivalence assumed'}
try:
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source screening'}),timeout=25) as r:
  b=r.read(12000001);assert len(b)<=12000000,'download cap';p.write_bytes(b);meta.update(status=r.status,final_url=r.url,headers=dict(r.headers),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
except Exception as e:meta.update(error=repr(e))
(E/(name+'.provenance.json')).write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps(meta))
