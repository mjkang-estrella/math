import pathlib,json,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1]; rec={'scope':'Path/metadata screens only, not semantic proof clearance','registries':{},'queries':[]}
terms=['grundy','zeckendorf','perfectmatching','taxicab','replacement','separatedcollection','matroidbased','conlon','katona','momentgraph','ehrhart']
for repo in ['Vilin97-lean-pool','openai-math','the-omega-institute-trureturing']:
 t=json.loads((D/f'sources/{repo}-tree/body').read_text());h=json.loads((D/f'sources/{repo}-head/body').read_text())['sha']
 paths=[x['path'] for x in t['tree']];rec['registries'][repo]={'head':h,'truncated':t.get('truncated'),'paths':len(paths),'hits':[p for p in paths if any(w in p.lower().replace('_','') for w in terms)]}
 print(repo,h,len(paths),t.get('truncated'));print('\n'.join(rec['registries'][repo]['hits'][:30]))
for p in sorted((D/'sources').glob('github-query-*/receipt.json')):
 x=json.loads(p.read_text());b=json.loads((p.parent/'body').read_text());rec['queries'].append({'receipt':str(p.relative_to(D)),**x,'count':b.get('total_count'),'hits':[z['full_name'] for z in b.get('items',[])]})
for p in (D/'sources').glob('pool-*/body'):
 lines=p.read_text().splitlines();hits=[{'line':j+1,'text':l[:500]} for j,l in enumerate(lines) if any(w in l.lower().replace('_','') for w in terms)]
 if hits:rec.setdefault('pool_metadata_hits',{})[str(p.relative_to(D))]=hits
(D/'outputs/registry-screen.json').write_text(json.dumps(rec,indent=2));print('metadata',[(x,len(y)) for x,y in rec.get('pool_metadata_hits',{}).items()]);print('queries',[(x['count'],x['hits']) for x in rec['queries']])
