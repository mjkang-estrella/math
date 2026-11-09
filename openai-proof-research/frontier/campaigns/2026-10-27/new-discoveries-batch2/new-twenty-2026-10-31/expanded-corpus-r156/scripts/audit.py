import pathlib,json,hashlib,os
p=pathlib.Path.cwd();r=json.loads((p/'results.json').read_text());v=json.loads((p/'reservation.json').read_text());assert len(r)==20 and set(r)==set(map(str,v['ids']))
for k,x in r.items():
 b=(p/x['raw_file']).read_bytes();assert b.endswith(b'\n');assert hashlib.sha256(b).hexdigest()==x['provenance']['raw_sha256'];assert hashlib.sha256(x['literal_statement'].encode()).hexdigest()==x['statement_sha256'];s=(p/'sources'/f'{k}.html').read_bytes();assert hashlib.sha256(s).hexdigest()==x['primary_receipt']['sha256']
manifest={str(f.relative_to(p)):hashlib.sha256(f.read_bytes()).hexdigest() for f in p.rglob('*') if f.is_file() and f.name!='manifest.json'}
(p/'outputs/manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print('PASS: exactly20 keys, all raw newlines/hashes, statement hashes,20 primary source hashes; files',len(manifest))
