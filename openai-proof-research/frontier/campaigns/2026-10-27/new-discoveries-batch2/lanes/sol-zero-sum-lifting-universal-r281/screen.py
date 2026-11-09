from pathlib import Path
import json,hashlib,datetime,urllib.request,urllib.parse,xml.etree.ElementTree as E
L=Path(__file__).resolve().parent;R=L.parents[6];old=L.parent/'sol-wide-discrete-algebraic-certificates-r277'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
bound=json.loads((old/'bindings.json').read_text()); screened=[]
for b in bound:
 p=Path(b['original'])
 if '/sources/cache/' not in str(p) or p.suffix!='.tex':continue
 assert h(p)==b['sha256']
 t=p.read_text();hits=[]
 for term in ['zero-sum','zero sum','reduced sequence','Letzter','Morrison','19965','18234']:
  start=0
  while (pos:=t.lower().find(term.lower(),start))>=0:
   hits.append({'term':term,'excerpt':t[max(0,pos-250):pos+650]});start=pos+len(term)
 assert h(p)==b['sha256'];screened.append({'path':str(p),'sha256':h(p),'hits':hits})
(L/'cached-body-screen.json').write_text(json.dumps(screened,indent=2))
print('Actual cached tex bodies screened:',len(screened),'bodies with hits:',sum(bool(x['hits']) for x in screened))
for name in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((L.parent.parent/name).read_text());print(name,'keys',list(d),'counts',d.get('accepted_count'),d.get('total_accepted_count'))
queries={'current-target':'id_list=2610.19965','primary-successors':'search_query='+urllib.parse.quote('all:"zero-sum problems of new types"')+'&start=0&max_results=30&sortBy=submittedDate&sortOrder=descending'}
for name,q in queries.items():
 u='https://export.arxiv.org/api/query?'+q;row={'url':u,'at':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=20) as f:d=f.read(1500000);row['status']=f.status
  p=L/(name+'.xml');p.write_bytes(d);row['sha256']=h(p);assert h(p)==row['sha256']
  tree=E.fromstring(d);ns={'a':'http://www.w3.org/2005/Atom'}
  row['entries']=[{k:e.findtext('a:'+k,namespaces=ns) for k in ['id','title','published','updated']} for e in tree.findall('a:entry',ns)]
 except Exception as e:row['failure']=repr(e)
 with (L/'access.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 print(name,row.get('entries',row.get('failure')))
