import urllib.request,pathlib,hashlib,datetime,json
p=pathlib.Path.cwd();log=[]
for key,u in [('codes-pdf','https://arxiv.org/pdf/2010.10762'),('codes-published','https://epub.uni-bayreuth.de/5128/1/max_minimal_codewords.pdf'),('lattice-published','https://combinatorialpress.com/article/jcmcc/volume%20126/perfect-truncated-metric-codes-in-lattice-graphs-and-superlattice-graphs.pdf'),('hypergraph-paper','https://mkwn.github.io/HCAA.pdf')]:
 try:
  with urllib.request.urlopen(u,timeout=15) as f:b=f.read()
  (p/'sources'/f'{key}.pdf').write_bytes(b);r={'key':key,'url':u,'status':200,'sha256':hashlib.sha256(b).hexdigest()}
 except Exception as e:r={'key':key,'url':u,'error':str(e)}
 r['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();log.append(r);print(r,flush=True)
 (p/'outputs/more-receipts.json').write_text(json.dumps(log,indent=2))
