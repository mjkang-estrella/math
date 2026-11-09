from pathlib import Path
import urllib.request,urllib.parse,json,hashlib,datetime,subprocess
R=Path(__file__).resolve().parent
out=R/'independent-sources';out.mkdir(exist_ok=True)
queries={
 'zero-preservers':'all:"polynomial" AND all:"Schur" AND all:"primes"',
 'exceptional':'ti:"exceptional polynomials"',
 'basins':'all:"Borisov" AND all:"fixed points"',
 'monomial':'ti:"cycle structure" AND all:"exponentiation"',
}
receipts=[]
for name,q in queries.items():
 url='https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':q,'max_results':8})
 row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:
   data=f.read(2000000);row.update(status=f.status,final_url=f.url)
  p=out/(name+'.xml');p.write_bytes(data);row.update(path=str(p),sha256=hashlib.sha256(data).hexdigest(),size=len(data))
 except Exception as e:row.update(error=repr(e))
 receipts.append(row)
(R/'retrieval-receipts.json').write_text(json.dumps(receipts,indent=2))
for row in receipts:print(row)
# Regenerate extracts directly from the frozen primary PDF bytes.
for name in ['original-borisov','borisov-precursor','borisov-follow']:
 subprocess.run(['pdftotext','-layout',str(R/'frozen-candidate/sources'/(name+'.pdf')),str(out/(name+'.txt'))],check=True)
