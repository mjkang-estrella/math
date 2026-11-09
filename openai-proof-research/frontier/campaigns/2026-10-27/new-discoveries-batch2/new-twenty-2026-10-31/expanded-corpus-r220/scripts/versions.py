import pathlib,json,re,sys
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import fetch,L
out={}
for r in json.loads((L/'reservation.json').read_text())['rows']:
 k=str(r['mathdb_id']);s=(L/'receipts'/f'{k}-abs.body').read_text();vs=sorted(set(map(int,re.findall(r'\[v(\d+)\]',s))));out[k]=vs
 for v in vs[:-1]:
  label=f'{k}-v{v}-html';fetch(r['source_url'].replace('/abs/','/html/')+f'v{v}',label)
  if json.loads((L/'receipts'/f'{label}.json').read_text()).get('status') in [403,429]:break
(L/'outputs/version-index.json').write_text(json.dumps(out,indent=2));print(out)
