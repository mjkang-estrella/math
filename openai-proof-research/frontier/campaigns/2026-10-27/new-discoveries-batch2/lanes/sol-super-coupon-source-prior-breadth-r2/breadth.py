from pathlib import Path
import xml.etree.ElementTree as E,json,hashlib,re,subprocess
from access import fetch
L=Path(__file__).resolve().parent;B=L.parent.parent
ns={'a':'http://www.w3.org/2005/Atom'}
entries=E.parse(L/'frozen-live/breadth2.xml').findall('a:entry',ns)
reports=[]
for p in (B/'lanes').iterdir():
 if not p.is_dir() or p==L:continue
 for name in ['SUMMARY.md','SCOUTING.md','review.md','discovery.md']:
  f=p/name
  if f.is_file():
   b=f.read_bytes();reports.append((str(f),hashlib.sha256(b).hexdigest(),b.decode(errors='replace')))
out=[]
for e in entries:
 id=e.findtext('a:id',namespaces=ns).rsplit('/',1)[-1];title=' '.join(e.findtext('a:title',namespaces=ns).split())
 # Identifier plus distinctive title phrase; do not infer clearing from no hit.
 aliases=[id.split('v')[0],title[:45].lower()]
 hits=[p for p,h,t in reports if any(a in t.lower() for a in aliases)]
 out.append(dict(id=id,title=title,authors=[x.text for x in e.findall('a:author/a:name',ns)],published=e.findtext('a:published',namespaces=ns),history_hits=hits))
(L/'history-screen2.json').write_text(json.dumps(dict(references=[dict(path=p,sha256=h) for p,h,t in reports],entries=out),indent=2)+'\n')
for r in out:
 print(r['id'],r['title'],'HITS',len(r['history_hits']))
 if not r['history_hits'] and r['id'] in ['2610.38893v1','2610.38877v1','2610.38510v1','2610.37618v1','2610.37521v1']:
  fetch(r['id']+'.pdf','https://arxiv.org/pdf/'+r['id'])
  f=L/'frozen-live'/(r['id']+'.pdf')
  if f.exists():
   p=L/'texts'/(r['id']+'.txt');p.parent.mkdir(exist_ok=True)
   subprocess.run(['pdftotext','-layout',str(f),str(p)],check=True)
