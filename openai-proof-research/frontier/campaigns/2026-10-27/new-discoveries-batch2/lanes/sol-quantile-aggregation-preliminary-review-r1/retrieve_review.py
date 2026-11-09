from pathlib import Path
import urllib.request,urllib.error,urllib.parse,json,hashlib,datetime
D=Path(__file__).resolve().parent
queries={'later-inclusion':'all:"quantile mixture" AND (all:counterexample OR all:aggregation)', 'joint-original':'ti:"Joint mixability" AND au:Wang', 'uniform-original':'ti:"Sums of uniform random variables"'}
urls={'joint-body':'https://pubsonline.informs.org/doi/pdf/10.1287/moor.2015.0755', 'uniform-body':'https://www.cambridge.org/core/services/aop-cambridge-core/content/view/S0021900219000524', 'uniform-arxiv':'https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':'ti:"Sums of standard uniform random variables"','max_results':5})}
for name,url in urls.items():
    rec={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'IndependentResearchReview/1.0'}),timeout=25) as r:
            data=r.read(3000000); rec.update(status=r.status,bytes=len(data),sha256=hashlib.sha256(data).hexdigest()); (D/(name+'.body')).write_bytes(data)
    except Exception as e: rec['failure']=str(e)
    with (D/'review-http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
    print(json.dumps(rec))
