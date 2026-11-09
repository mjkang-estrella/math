import pathlib,json,hashlib,re
D=pathlib.Path(__file__).resolve().parents[1];x=json.loads((D/'results.json').read_text());r=json.loads((D/'reservation.json').read_text())
assert set(map(int,x))==set(r['ids']) and len(x)==20
for i,o in x.items():
 b=(D/'raw'/f'{i}.jsonl').read_bytes();assert b.endswith(b'\n');assert hashlib.sha256(b).hexdigest()==o['provenance']['raw_sha256'];assert hashlib.sha256(o['statement'].encode()).hexdigest()==o['provenance']['statement_utf8_sha256'];assert o['accepted_credit']==0 and o['lean_endpoint'] is None
for p in (D/'sources').glob('*.receipt.json'):
 o=json.loads(p.read_text());f=p.with_name(p.name.removesuffix('.receipt.json'))
 if 'sha256' in o:assert f.exists() and hashlib.sha256(f.read_bytes()).hexdigest()==o['sha256']
p=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/preprints-tree.json');o=json.loads(p.read_text());s=json.dumps(o)
(D/'logs/pinned-preprints-check.json').write_text(json.dumps({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':len(s),'title_terms':['pinnable','transitive partitions','NV2','square-energy','remoteness'],'matching_paths':[z.get('path') for z in (o.get('tree',[]) if isinstance(o,dict) else o) if isinstance(z,dict) and re.search('pinnab|transitive.partition|NV2|square.energy|remoteness',z.get('path',''),re.I)]},indent=2)+'\n')
versions=list((D/'sources').glob('*v[0-9].pdf'))
res={'entries':len(x),'raw_hashes':'pass','HTTP_body_hashes':'pass','versioned_source_PDFs':len(versions),'Lean_endpoints':0,'credit':0,'resource_receipts':len(list((D/'logs').glob('*.receipt.json')))}
(D/'validation.json').write_text(json.dumps(res,indent=2)+'\n');print(res)
