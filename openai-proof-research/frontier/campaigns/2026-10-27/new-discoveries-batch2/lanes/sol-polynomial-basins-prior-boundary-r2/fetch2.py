exec((__import__('pathlib').Path(__file__).parent/'retrieve.py').read_text().split('queries=')[0])
import subprocess
queries=[('citing-set','https://api.openalex.org/works?filter=cites:W2336937078&per-page=20'),('localnilpotent','https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':'all:"locally nilpotent" AND (all:"polynomial" OR all:"integer")','max_results':15})),('kps','https://arxiv.org/pdf/math/9911094v1'),('iterated-identities','https://arxiv.org/pdf/1710.04084v2')]
receipts=[]
for name,url in queries:
 r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical-source-review/1.0'}),timeout=35) as f:
   data=f.read(6000000);r.update(status=f.status,final_url=f.url)
  q=L/'retrieved'/(name+('.pdf' if '/pdf/' in url else '.json' if 'openalex' in url else '.xml'));q.write_bytes(data);r.update(path=str(q.relative_to(L)),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),frozen_before_read=True)
  (L/'retrieved'/(name+'.freeze.json')).write_text(json.dumps(r,indent=2)+'\n')
  if q.suffix=='.pdf':
   out=q.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(q),str(out)],check=True,timeout=30);r.update(text=str(out.relative_to(L)),text_sha256=hashlib.sha256(out.read_bytes()).hexdigest())
 except Exception as e:r.update(error=str(e),stop_no_retry=True)
 receipts.append(r)
(L/'retrieval2.json').write_text(json.dumps(receipts,indent=2)+'\n')
print(json.dumps(receipts,indent=2))
