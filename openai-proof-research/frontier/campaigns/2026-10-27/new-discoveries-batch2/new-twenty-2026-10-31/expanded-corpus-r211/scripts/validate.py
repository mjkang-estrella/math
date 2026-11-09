import pathlib,json,hashlib,collections
D=pathlib.Path(__file__).resolve().parents[1];r=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert len(r)==20 and set(r)==set(map(str,ids));assert all(v['lean_endpoint'] is None and v['discovery_credit']==0 for v in r.values())
for i,v in r.items():
 b=(D/'raw'/f'{i}.jsonl').read_bytes();assert b.endswith(b'\n');assert hashlib.sha256(b).hexdigest()==v['provenance']['raw_sha256'];assert hashlib.sha256(v['statement'].encode()).hexdigest()==v['provenance']['statement_utf8_sha256']
for p in (D/'sources').glob('*.receipt.json'):
 o=json.loads(p.read_text());f=p.with_name(p.name[:-13])
 if 'sha256' in o:assert f.exists() and hashlib.sha256(f.read_bytes()).hexdigest()==o['sha256'],str(p)
for name in ['SUMMARY.md','CANDIDATE.md']:assert (D/name).stat().st_size>100
for k in ['7','9','11']:
 a=json.loads((D/f'outputs/nim-{k}.json').read_text());assert all(x['P1wins'] for x in a);print('nim',k,'completed',a[0]['tokens'],a[-1]['tokens'],len(a))
summary={'ID_count':20,'outcomes':dict(collections.Counter(v['outcome'] for v in r.values())),'credit':0,'status':'artifact consistency checks pass; no full theorem or discovery acceptance claimed'}
(D/'outputs/validation.json').write_text(json.dumps(summary,indent=2)+'\n');print(summary)
