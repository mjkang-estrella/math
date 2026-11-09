from pathlib import Path
import json,urllib.request,urllib.parse,datetime,hashlib
L=Path(__file__).resolve().parent
queries=[('arxiv-title','https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':'ti:"visible points" AND (all:parallelogram OR all:Khan)','max_results':12})),('openalex','https://api.openalex.org/works?'+urllib.parse.urlencode({'search':'A Conjectural Inequality for Visible Points in Lattice Parallelograms','per-page':8})),('registry','https://api.github.com/repos/openai/math/commits?per_page=1')]
# GitHub deliberately not attempted: known route denial is binding.
for label,url in queries[:2]:
 rec={'label':label,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research-source-check/1.0'}),timeout=22) as r:
   raw=r.read(2500000);rec.update(status=r.status,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
  p=L/(label+'.body');p.write_bytes(raw)
 except Exception as e:rec['failure']=str(e)
 with (L/'access.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(json.dumps(rec))
