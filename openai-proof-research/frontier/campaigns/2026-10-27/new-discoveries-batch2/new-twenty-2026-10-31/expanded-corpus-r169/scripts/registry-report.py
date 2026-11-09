import pathlib,json,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1];ex=json.loads((D/'extracted.json').read_text());terms=[*ex]+[o['source_url'].split('/')[-1] for o in ex.values()]+['Havet','Horsch','Hörsch','Rambaud','Cafure','Saito','Woei','Cameron','Pulaj','Kamyczu','Przyby','Mühle','Mousavi','Bodirsky','Pinsker','Bergelson','Hindman','Leader','Thraves','Komarov','Mackey','equitable total','inversion diameter','conflict-free','precoloring','common radical','distance-dominating','permutation trinomial','Rote-Fibonacci']
out={'utc':'2026-11-04','terms':terms,'registries':{},'github_queries':[],'limits':'Path screens and projects/candidate text screens only; negative findings are not worldwide clearance.'}
for key in ['pool','omega','openai']:
 p=D/f'sources/{key}-head.json'
 if not p.exists():continue
 head=json.loads(p.read_text())['sha'];tree=json.loads((D/f'sources/{key}-tree.json').read_text());hits=[]
 for row in tree.get('tree',[]):
  ts=[t for t in terms if t.lower() in row['path'].lower()]
  if ts:hits.append({'path':row['path'],'terms':ts})
 out['registries'][key]={'head':head,'truncated':tree.get('truncated'),'paths':len(tree.get('tree',[])),'hits':hits}
poolhits=[]
for p in (D/'sources').glob('pool-*'):
 if p.suffix=='.json':continue
 for n,l in enumerate(p.read_text().splitlines(),1):
  ts=[t for t in terms if t.lower() in l.lower()]
  if ts:poolhits.append({'file':p.name,'line':n,'terms':ts,'text':l[:1000]})
out['pool_text_hits']=poolhits
for r in json.loads((D/'outputs/fetch-github.json').read_text()):
 j=len(out['github_queries']);p=D/f'sources/github-query-{j}.json';o=json.loads(p.read_text()) if p.exists() else {};out['github_queries'].append({**r,'total_count':o.get('total_count'),'hits':[{'name':x['full_name'],'description':x.get('description')} for x in o.get('items',[])]})
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2,ensure_ascii=False));print(json.dumps(out,ensure_ascii=False)[:10000])
