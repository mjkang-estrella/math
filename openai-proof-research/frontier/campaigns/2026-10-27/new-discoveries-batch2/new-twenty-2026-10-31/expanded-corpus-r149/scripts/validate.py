import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parents[1]
d=json.loads((L/'results.json').read_text());ids=json.loads((L/'reservation.json').read_text())['ids']
assert set(d)==set(map(str,ids)) and len(d)==20
checks=0
for i,v in d.items():
 b=(L/v['raw_file']).read_bytes()
 assert b.endswith(b'\n')
 assert hashlib.sha256(b).hexdigest()==v['provenance']['raw_sha256']
 r=json.loads(b)
 assert r['statement']==v['literal_statement']
 assert hashlib.sha256(r['statement'].encode()).hexdigest()==v['statement_sha256']
 for receipt in v['source_receipts']:
  kind=receipt['url'].split('/')[-2]
  if 'sha256' in receipt:
   assert hashlib.sha256((L/f'sources/{i}.{kind}').read_bytes()).hexdigest()==receipt['sha256'];checks+=1
 assert v['credit']==0 and not v['accepted']
assert (L/'SUMMARY.md').stat().st_size>1000
extra=[]
for name,url in [
 ('kl-intro.tex','https://raw.githubusercontent.com/openai/math/4eaee87548250b2682affda7d05d947c05554bae/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/build/01-introduction.tex'),
 ('rsk-successor.pdf','https://arxiv.org/pdf/2602.18612'),
 ('polychrom-II.pdf','https://arxiv.org/pdf/2604.24412')]:
 p=L/'sources'/name
 extra.append(dict(path=str(p.relative_to(L)),url=url,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),body_saved_utc=datetime.datetime.fromtimestamp(p.stat().st_mtime,datetime.timezone.utc).isoformat(),status='HTTP headers retained separately; successful body parsed'))
(L/'outputs/supplemental-source-receipts.json').write_text(json.dumps(extra,indent=2)+'\n')
manifest={str(p.relative_to(L)):hashlib.sha256(p.read_bytes()).hexdigest() for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','validation.json','validation.log']}
(L/'outputs/manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
v=dict(entries=20,raw_newline_and_hash_checks=20,current_source_body_hash_checks=checks,accepted=0,candidates=0,independent_review='not performed',lean_endpoint='none',utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(L/'outputs/validation.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps(v,indent=2))
