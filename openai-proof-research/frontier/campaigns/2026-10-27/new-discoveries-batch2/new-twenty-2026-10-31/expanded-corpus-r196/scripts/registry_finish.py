import sys,pathlib,json,re
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import fetch,D
p=D/'outputs/registry-screen.json';out=json.loads(p.read_text());rows=json.loads((D/'reservation.json').read_text())['rows']
terms=[str(r['mathdb_id']) for r in rows]+[r['source_url'].rsplit('/',1)[1] for r in rows]+['Gao','Derycke','Dukes','Le Borgne','Mikulincer','Stanley','Yan','Neuwohner','Golafshan','Whiteland','Dobrovolska','Nakamuta','Bezrukov','Bulatovic','Kuzmanovski','Gurevich','Zhong','Kravitz','Bryant','sign.smoothing','wall.crossing','CTI','ITC','isoperimetric','Kekul','pebbling','geodetic','monadic']
rx=re.compile('|'.join(terms),re.I);out['pool_keyword_hits']=[]
for r in out['receipts']:
 if '/raw.githubusercontent.com/Vilin97/lean-pool/' in r['url'] and r['status']==200:
  lines=pathlib.Path(r['body']).read_text().splitlines()
  for n,line in enumerate(lines,1):
   if rx.search(line):out['pool_keyword_hits'].append({'body':r['body'],'line':n,'text':line})
for q in out['queries']:
 z=q['receipt']
 if z['status']==200:q['hits']=[{'name':x['full_name'],'description':x.get('description')} for x in json.loads(pathlib.Path(z['body']).read_text())['items']]
for repo,sha in out['heads'].items():
 if repo=='Vilin97/lean-pool':continue
 z=fetch(f'https://api.github.com/repos/{repo}/git/trees/{sha}','registry-root-'+repo.split('/')[0]);out['receipts'].append(z)
 if z['status']!=200:continue
 for node in json.loads(pathlib.Path(z['body']).read_text())['tree']:
  if node['path'] not in ('D5','Problems','preprints'):continue
  w=fetch(f'https://api.github.com/repos/{repo}/git/trees/{node["sha"]}?recursive=1','registry-scope-'+node['path']);out['receipts'].append(w)
  if w['status']==200:
   b=json.loads(pathlib.Path(w['body']).read_text());out.setdefault('path_screens',[]).append({'repo':repo,'scope':node['path'],'truncated':b.get('truncated'),'count':len(b['tree']),'hits':[x['path'] for x in b['tree'] if rx.search(x['path'])]})
out['limits']='Keyword and path screens only; no all-proof-body clearance. Broad surname hits are not matches to exact conjectures. Search eight queries with seven-second spacing.'
p.write_text(json.dumps(out,indent=2));print('pool hits',len(out['pool_keyword_hits']));print([(q['query'],q.get('hits')) for q in out['queries']]);print(out.get('path_screens'))
