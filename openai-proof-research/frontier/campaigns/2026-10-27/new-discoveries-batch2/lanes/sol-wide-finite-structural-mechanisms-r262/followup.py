from explore import *
from urllib.parse import urlencode
ns={'a':'http://www.w3.org/2005/Atom'}
for key,q in [('cores2','all:"self-conjugate" AND all:"cores"'),('schur2','au:"Koutschan" AND au:"Wong"'),('irred','all:"irredundance" AND all:"product"')]:
 p=L/(key+'.xml');url='https://export.arxiv.org/api/query?'+urlencode(dict(search_query=q,max_results=30,sortBy='lastUpdatedDate',sortOrder='descending'))
 if fetch(url,p):
  a=[{k:e.findtext('a:'+k,namespaces=ns) for k in ['id','title','summary','published','updated']} for e in E.parse(p).findall('a:entry',ns)]
  (L/(key+'.json')).write_text(json.dumps(a,indent=2));print(key,[(d['id'],d['title'],d['summary'][:350]) for d in a])
for ident in ['1609.07639v2','2605.03284v2','2410.14063v2']:
 p=L/'sources'/(ident+'.pdf')
 if fetch('https://arxiv.org/pdf/'+ident,p):
  h=digest(p);t=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True,timeout=25);assert digest(p)==h
  with (L/'bindings.jsonl').open('a') as f:f.write(json.dumps(dict(id=ident,pdf=str(p),pdf_sha256=h,text=str(t),text_sha256=digest(t)))+'\n')
