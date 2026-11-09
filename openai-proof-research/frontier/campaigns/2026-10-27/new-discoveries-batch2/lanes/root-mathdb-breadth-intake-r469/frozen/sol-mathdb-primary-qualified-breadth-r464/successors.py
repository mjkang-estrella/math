import urllib.request,urllib.parse,json,pathlib,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent
qs=['all:"simultaneous core partitions" AND all:"average"','all:"Hyatt" AND all:"unimodality"','all:"universal dynamics monoid"','all:"balanced decomposition"']
out=[]
for i,q in enumerate(qs):
 u='https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':q,'max_results':8,'sortBy':'submittedDate','sortOrder':'descending'});r={'url':u,'query':q,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'version':'Atom query response; metadata only'}
 try:
  with urllib.request.urlopen(u,timeout=15) as f:d=f.read(500000);r['status']=f.status
  p=L/'sources'/f'successors-{i}.xml';p.write_bytes(d);r.update(path=str(p),sha256=hashlib.sha256(d).hexdigest())
 except Exception as e:r['failure']=str(e);out.append(r);break
 out.append(r)
(L/'successors.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
