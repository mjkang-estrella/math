import pathlib,json,hashlib,resource,time
L=pathlib.Path(__file__).resolve().parent
h=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((L/'reservation.json').read_text());j=json.loads((L/'results.json').read_text())
assert len(j)==20 and set(j)==set(map(str,r['ids']))
assert h((L/'reservation.json').read_bytes())==(L/'reservation.sha256').read_text().strip()
for k,v in j.items():
 b=(L/v['raw_file']).read_bytes();assert b.endswith(b'\n');assert h(b)==v['raw_sha256']
 assert h(v['literal_statement'].encode())==v['statement_sha256'];assert json.loads(b)==v['literal_record']
 p=pathlib.Path(v['chunk']); assert h(p.read_bytes())==v['chunk_sha256']
 assert p.read_bytes().splitlines(keepends=True)[v['line_one_based']-1]==b
for s in (L/'source-receipts.jsonl').read_text().splitlines():
 a=json.loads(s)
 if 'path' in a:assert h((L/a['path']).read_bytes())==a['sha256']
for a in json.loads((L/'reused-registry-manifest.json').read_text()):assert h(pathlib.Path(a['path']).read_bytes())==a['sha256']
(L/'validation.json').write_text(json.dumps({'exact_20_ids':True,'all_raw_chunk_statement_bindings':True,'all_source_receipt_hashes':True,'reused_registry_hashes':True,'reservation_unchanged':True,'maxrss_KiB_this_validation_only':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'accepted_credit':0},indent=2)+'\n')
lines=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name!='SHA256SUMS':lines.append(h(p.read_bytes())+'  '+str(p.relative_to(L)))
(L/'SHA256SUMS').write_text('\n'.join(lines)+'\n')
print('PASS: fixed20, all provenance, receipt and reused-input hashes;',len(lines),'artifacts')
