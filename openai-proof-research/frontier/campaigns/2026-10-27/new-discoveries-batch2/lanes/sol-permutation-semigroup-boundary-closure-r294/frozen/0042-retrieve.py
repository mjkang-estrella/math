from pathlib import Path
import urllib.request,urllib.parse,hashlib,json,time,sys
L=Path(__file__).resolve().parent;D=L/'sources';D.mkdir(exist_ok=True)
jobs={
 'successors':'https://export.arxiv.org/api/query?search_query='+urllib.parse.quote('all:"permutation numerical semigroups"')+'&max_results=20',
 'citing':'https://api.openalex.org/works/https://doi.org/10.48550/arXiv.1609.01133',
 'breadth':'https://export.arxiv.org/api/query?search_query='+urllib.parse.quote('(ti:conjecture OR ti:conjectures) AND submittedDate:[20100101 TO 20231231] AND (cat:math.CO OR cat:math.NT)')+'&start=150&max_results=32',
}
if len(sys.argv)>1:jobs=json.loads(sys.argv[1])
log=json.loads((L/'access.json').read_text()) if (L/'access.json').exists() else []
for name,url in jobs.items():
 r={'name':name,'url':url,'time_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'MathematicalResearch/1.0'})
  with urllib.request.urlopen(req,timeout=22) as f: data=f.read(6000000);r['status']=f.status
  p=D/name;p.write_bytes(data);r.update(path=str(p),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
 except Exception as e:r['error']=str(e)
 log.append(r);(L/'access.json').write_text(json.dumps(log,indent=2));print(r,flush=True)
