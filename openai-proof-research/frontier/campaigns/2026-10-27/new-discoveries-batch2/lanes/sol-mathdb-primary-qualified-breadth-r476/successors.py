import urllib.request,urllib.parse,urllib.error,pathlib,json,datetime,hashlib,xml.etree.ElementTree as E,time
D=pathlib.Path(__file__).resolve().parent
queries=[('336929','all:"EKR-module"'),('337870','all:"hypercube" AND all:"intersection"'),('337854','all:"regularity" AND all:"minimum distance"'),('337624','all:"convex" AND all:"dimension one"'),('336790','all:"Berkovich" AND all:"Uncu" AND all:"inequalities"')]
blocked=False
with (D/'successor-access.jsonl').open('x') as log:
 for key,q in queries:
  u='https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':q,'start':0,'max_results':5,'sortBy':'submittedDate','sortOrder':'descending'})
  r={'mathdb_id':int(key),'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'bounded metadata discovery only; no novelty inference'}
  if blocked:r['status']='HOLD not attempted after access stop'
  else:
   try:
    with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'MathResearchScreen/1.0'}),timeout=15) as response:b=response.read(2000000)
    p=D/'sources'/('successors-'+key+'.xml');p.write_bytes(b);r.update(file=str(p.relative_to(D)),sha256=hashlib.sha256(b).hexdigest(),status='metadata_only')
    ns={'a':'http://www.w3.org/2005/Atom'};root=E.fromstring(b);r['entries']=[{'id':x.findtext('a:id',namespaces=ns),'title':x.findtext('a:title',namespaces=ns),'summary':x.findtext('a:summary',namespaces=ns)} for x in root.findall('a:entry',ns)]
   except urllib.error.HTTPError as e:r.update(status='HOLD_HTTP',http_status=e.code,error=str(e));blocked=e.code in (403,429)
   except Exception as e:r.update(status='HOLD_ERROR',error=repr(e))
   time.sleep(1)
  log.write(json.dumps(r)+'\n');log.flush();print(json.dumps(r),flush=True)
