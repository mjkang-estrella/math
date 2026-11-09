import pathlib,concurrent.futures,json,re
r=pathlib.Path(__file__).resolve().parent
ns={'__file__':str(r/'fetch.py')};exec(compile((r/'fetch.py').read_text().split('mode=sys.argv')[0],str(r/'fetch.py'),'exec'),ns)
jobs=[('registry-pool-projects.yml','https://raw.githubusercontent.com/Vilin97/lean-pool/HEAD/LeanPool/projects.yml'),('registry-pool-index.lean','https://raw.githubusercontent.com/Vilin97/lean-pool/HEAD/LeanPool.lean'),('registry-omega-head.html','https://github.com/teorth/omega')]
for name,arxiv in [('343137-companion','1306.5970'),('374916-companion1','2507.00515'),('374916-companion2','2003.10161'),('citing-removal','2609.20237'),('citing-precolor','2310.09973')]:
 s=(r/'sources'/(name+'.abs.html')).read_text();vs=sorted(set(re.findall(r'\[v(\d+)\]',s)),key=int)
 for v in vs:jobs.append((name+'v'+v+'.pdf','https://arxiv.org/pdf/'+arxiv+'v'+v))
receipts=[]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 for rec in pool.map(ns['get'],jobs):receipts.append(rec);print(json.dumps(rec),flush=True)
(r/'receipts-supplement.json').write_text(json.dumps(receipts,indent=2)+'\n')
