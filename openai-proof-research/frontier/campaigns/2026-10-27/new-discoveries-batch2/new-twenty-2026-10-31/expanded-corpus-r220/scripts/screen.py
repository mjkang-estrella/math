import pathlib,json,re
L=pathlib.Path(__file__).resolve().parents[1]; rows=json.loads((L/'reservation.json').read_text())['rows'];out={}
for r in rows:
 k=str(r['mathdb_id']); terms=[k,r['source_url'].split('/')[-1]]
 out[k]={}
 for p in (L/'receipts').glob('pool-file-*.body'):
  hits=[]
  for i,line in enumerate(p.read_text().splitlines(),1):
   if any(t.lower() in line.lower() for t in terms):hits.append({'line':i,'text':line[:600]})
  if hits:out[k][p.name]=hits
print(json.dumps(out,indent=2));(L/'outputs/registry-screen.json').write_text(json.dumps({'leanpool_head':json.loads((L/'receipts/leanpool-head.body').read_text())['sha'],'id_arxiv_hits':out,'limitation':'Initial ID and arXiv screen; authors and keywords pending; no proof clearance.'},indent=2))
