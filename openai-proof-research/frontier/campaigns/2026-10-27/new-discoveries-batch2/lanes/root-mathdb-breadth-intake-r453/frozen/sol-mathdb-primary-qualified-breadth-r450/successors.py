import pathlib,urllib.request,urllib.parse,urllib.error,datetime,hashlib,json
L=pathlib.Path(__file__).resolve().parent;log=[]
queries=['rainbow cycles logarithmic average degree','conforming finite element arbitrary dimension','complicial sets cellular comparison','submodular k partition polynomial','residually nilpotent orthogonal quantum groups']
for i,q in enumerate(queries):
 u='https://arxiv.org/search/?'+urllib.parse.urlencode({'query':q,'searchtype':'all','abstracts':'show','order':'-announced_date_first','size':50});e={'query':q,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=18) as r:b=r.read(1500000);e['status']=r.status
  p=L/'sources'/('successor-search-'+str(i)+'.html');p.write_bytes(b);e.update(file=str(p.relative_to(L)),sha256=hashlib.sha256(b).hexdigest())
 except Exception as ex:
  e.update(status='HOLD',error=str(ex));log.append(e)
  if isinstance(ex,urllib.error.HTTPError) and ex.code in [403,429]:break
  continue
 log.append(e)
(L/'successor-access.json').write_text(json.dumps(log,indent=2)+'\n');print(json.dumps(log,indent=2))
