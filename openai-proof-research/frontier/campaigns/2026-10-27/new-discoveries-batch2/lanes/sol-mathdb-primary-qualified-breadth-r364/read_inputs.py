exec((__import__('pathlib').Path(__file__).parent/'freeze.py').read_text().split("names=")[0])
def check(p,e):assert (e.get('size',e.get('bytes')) is None or p.stat().st_size==e.get('size',e.get('bytes'))) and h(p)==e['sha256'],str(p)
for e in json.loads((R/'bindings.json').read_text())['files']:check(Path(e['path']),e)
for name in ['root-mathdb-cayley-review-intake-r363','root-mathdb-accepted-exclusions-r304']:
 d=L/name;m=json.loads((d/'manifest.json').read_text());m=m['files'] if isinstance(m,dict) else m
 if isinstance(m,dict):m=[dict(v,path=k) for k,v in m.items()]
 for e in m:check(d/e['path'],e)
 print('manifest validated',name,len(m))
d=L/'pi-mathdb-full-corpus-inventory-r301';m=json.loads((d/'manifest.json').read_text());chunks=[e for e in m['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20
for e in chunks:check(d/e['path'],e)
root=L/'root-mathdb-cayley-review-intake-r363';ids=json.loads((root/'reserved-ids.json').read_text())['ids'];cov=json.loads((root/'coverage-delta.json').read_text());assert len(cov)==583
sets=[set(json.loads((L/n/'reserved-ids.json').read_text())['ids']) for n in ['root-mathdb-breadth-intake-r361','root-mathdb-gram-intake-r359']];assert all(len(s)==50 for s in sets)
assert len(ids)==len(set(ids))==50 and not set(ids)&set(map(int,cov)) and not set(ids)&(sets[0]|sets[1]) and not sets[0]&sets[1]
assert all(not s&set(map(int,cov)) for s in sets)
ex=json.loads((L/'root-mathdb-accepted-exclusions-r304'/'accepted-exclusions.json').read_text());hist=json.loads((L/'root-mathdb-accepted-exclusions-r304'/'historical-dispositions.json').read_text())
print('r304',json.dumps(ex)[:900]);print('history',json.dumps(hist)[:2200]);print('upstream',Path('openai-proof-research/sources/upstream.json').read_text());print('context', (L.parent/'prior-campaign-context.json').read_text()[:1300]);print('ledger', (L.parent/'ledger.json').read_text()[:500])
records=[]
for e in chunks:
 for line_no,line in enumerate((d/e['path']).open(),1):
  x=json.loads(line)
  if int(x.get('mathdb_id',x.get('id',-1))) in ids:records.append({'path':str(d/e['path']),'line':line_no,'record':x})
assert len(records)==50
(R/'record-refs.json').write_text(json.dumps([{k:v for k,v in a.items() if k!='record'}|{'id':a['record'].get('mathdb_id',a['record'].get('id'))} for a in records],indent=2)+'\n')
for a in records:
 print('\nRECORD',json.dumps(a['record'],ensure_ascii=False))
