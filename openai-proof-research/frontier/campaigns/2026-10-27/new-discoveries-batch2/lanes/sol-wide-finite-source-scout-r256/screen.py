import json,re,subprocess,urllib.parse,hashlib
from retrieve import fetch,L
ids=['1901.00084','1901.02479','1901.03112','1901.03451','1602.00208','1603.00673','2301.02041','2301.04428','2301.06242','2401.08271','2401.09497','2401.11152','2401.12883']
entries=json.loads((L/'entries.json').read_text());hist=(L/'history-index.txt').read_text();cat=(L/'frozen/sources--CONTENTS.md').read_text()
rows=[]
for id in ids:
 r=next(e for e in entries if id in e['id']);version=r['id'].split('/')[-1]
 terms=[id,r['title'].strip()]+[a.split()[-1] for a in r['authors']]
 hits={t:[m.start() for m in re.finditer(re.escape(t),hist,re.I)][:12] for t in terms}
 row=dict(r,history_hits=hits,catalogue_title_hit=r['title'].lower() in cat.lower());rows.append(row)
 print(id,r['title'],'HISTORY',hits)
 # Exact current title is already returned by current arXiv feed; search for successor titles/abstract mentions too.
 q='all:"'+r['title'].replace('$','').replace('\\','').strip()+'"'
 fetch('https://export.arxiv.org/api/query?'+urllib.parse.urlencode(dict(search_query=q,start=0,max_results=8)),id+'-exact.xml')
 fetch('https://arxiv.org/pdf/'+version,id+'.pdf')
 p=L/'sources'/(id+'.pdf')
 if p.exists():
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
  s=p.with_suffix('.txt').read_text()
  excerpts=[]
  for m in re.finditer(r'(?i)conjectur|question\s+\d|problem\s+\d',s):excerpts.append(s[max(0,m.start()-180):m.start()+1800])
  (L/'sources'/(id+'-excerpts.txt')).write_text('\n\n'.join(excerpts))
  print('BODY',id,'pages',s.count('\f'),'conjecture excerpts',len(excerpts))
(L/'early-screen.json').write_text(json.dumps(rows,indent=2))
