import pathlib,json,re,subprocess,sys,urllib.parse
D=pathlib.Path(__file__).resolve().parents[1]
def get(n,u):subprocess.run([sys.executable,'-I',str(D/'scripts/fetch.py'),n,u],check=True)
sha=json.loads((D/'sources/leanpool-head.json').read_text())['sha']
tree=json.loads((D/'sources/leanpool-tree.json').read_text())
for x in tree['tree']:
 p=x['path']
 if p=='LeanPool/projects.yml' or (p.startswith('candidates/') and x['type']=='blob'):
  get('pool-'+p.replace('/','_'),f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/{p}')
terms=['Taranenko','Deficiency','ExtremalMatrices','Loupekine','Berman','Oliveros','Ulrich','Coskun','Svinin','Faulhaber','Disparate','Platonic','StrictCorner','Alexandersson','Panova','Kite','Stahl','Brualdi','Stein','Buratti','Ingleton','Harremoes','Bennequin','Mortada','Saturated','Transversals','MinimalCovers','AdditiveUniqueness','LeeCode']
terms += [str(o['mathdb_id']) for o in json.loads((D/'extracted.json').read_text()).values()]
terms += [o['source_url'].split('/')[-1] for o in json.loads((D/'extracted.json').read_text()).values()]
out={}
for label in ['leanpool','omega','openai']:
 t=json.loads((D/'sources'/f'{label}-tree.json').read_text())
 out[label]={'head':json.loads((D/'sources'/f'{label}-head.json').read_text())['sha'],'truncated':t['truncated'],'path_hits':[x['path'] for x in t['tree'] if any(w.lower() in x['path'].lower() for w in terms)]}
for p in (D/'sources').glob('pool-*'):
 if p.name.endswith('receipt.json'):continue
 hits=[{'line':i,'text':l[:1500]} for i,l in enumerate(p.read_text().splitlines(),1) if any(w.lower() in l.lower() for w in terms)]
 if hits:out[p.name]=hits
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2)[:20000])
