import sys
args=sys.argv[:];sys.argv=[sys.argv[0],'import']
import research as r,subprocess
sys.argv=args
ids=['2502.02989v2','2502.13819v2','2608.17927v3','2608.02288v2','2609.28707v1','2608.11686v2','2609.23051v1','2609.11418v2']
for id in ids:
 p=r.L/'retrieval'/(id+'.pdf')
 if not p.exists():r.fetch('https://arxiv.org/pdf/'+id,id+'.pdf')
 if not p.exists():continue
 h=r.sha(p);q=p.with_suffix('.txt')
 if not q.exists():
  subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True)
  assert r.sha(p)==h
  r.save({'url':'https://arxiv.org/pdf/'+id,'pdf_sha256':h,'text_sha256':r.sha(q)},q.with_suffix('.freeze.json'))
 print(id,'frozen')
