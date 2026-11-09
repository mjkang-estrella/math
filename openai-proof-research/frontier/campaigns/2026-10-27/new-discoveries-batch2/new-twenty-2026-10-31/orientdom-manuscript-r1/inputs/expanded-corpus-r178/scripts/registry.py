import sys,pathlib,json,time,urllib.parse,re
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import fetch,D
out={'queries':[],'heads':{},'hits':[]}
for repo in ['Vilin97/lean-pool','openai/math','the-omega-institute/trureturing']:
 name=repo.split('/')[-1];r=fetch('https://api.github.com/repos/'+repo+'/commits/HEAD',name+'-head.json');out['heads'][repo]=r
 if r['status']!=200:continue
 sha=json.loads((D/'sources'/(name+'-head.json')).read_text())['sha'];out['heads'][repo]['sha']=sha
 if repo=='Vilin97/lean-pool':
  t=fetch('https://api.github.com/repos/'+repo+'/git/trees/'+sha+'?recursive=1','lean-pool-tree.json')
  if t['status']==200:
   tree=json.loads((D/'sources/lean-pool-tree.json').read_text())['tree']
   for item in tree:
    p=item['path']
    if item['type']=='blob' and (p.endswith('projects.yml') or p.startswith('candidates/')):
     out.setdefault('files',[]).append(fetch('https://raw.githubusercontent.com/'+repo+'/'+sha+'/'+p,'pool-'+p.replace('/','__')))
queries=['"subtraction" "lean"','"orientable total domination" lean','"cochordal" lean','"cube-width" lean','"2312.02426" lean','"2311.02430" lean','"upcycles" lean','"Schur" "interval" lean']
for q in queries:
 r=fetch('https://api.github.com/search/repositories?q='+urllib.parse.quote(q),'ghquery'+str(len(out['queries']))+'.json');r['query']=q;out['queries'].append(r)
 if r['status']!=200:break
 time.sleep(8)
rows=json.loads((D/'reservation.json').read_text())['rows'];terms=[str(r['mathdb_id']) for r in rows]+[r['source_url'].rsplit('/',1)[1] for r in rows]+['Miklós','Miklos','Post','Dravec','Kuenzel','Deshpande','cochord','cube-width','upcycle','Taziki','Gharakhloo','Tokareva','Khesin','Schur']
for p in (D/'sources').glob('pool-*'):
 if p.name.endswith('receipt.json'):continue
 for n,line in enumerate(p.read_text(errors='replace').splitlines(),1):
  hits=[t for t in terms if t.lower() in line.lower()]
  if hits:out['hits'].append({'file':p.name,'line':n,'terms':hits,'text':line})
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2))
