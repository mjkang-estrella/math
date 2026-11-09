from pathlib import Path
import hashlib,json,sys,tarfile
L=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
manifest=json.loads((L/'manifest.json').read_text())
excluded={'manifest.json','verification-receipt.json'}
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in excluded}
assert actual==set(manifest['files']),{'missing':sorted(set(manifest['files'])-actual),'extra':sorted(actual-set(manifest['files']))}
for name,r in manifest['files'].items():
 b=(L/name).read_bytes();assert len(b)==r['size'] and sha(b)==r['sha256'],name
bound=0
for name in ['input-bindings.json','administrative-bindings.json','audit-tool-binding.json']:
 rows=json.loads((L/name).read_text());rows=rows if isinstance(rows,list) else [rows]
 for r in rows:
  b=Path(r['path']).read_bytes();assert len(b)==r['size'] and sha(b)==r['sha256'],r['path'];bound+=1
sources=json.loads((L/'source-manifest.json').read_text())
for n,h in sources.items():
 assert sha((L/n).read_bytes())==h,n
 assert sha((L/'fresh-replay'/n).read_bytes())==h,n
with tarfile.open(L/'source-only.tar.gz') as t:
 assert sorted(t.getnames())==sorted(list(sources)+['source-manifest.json'])
 for member in t:
  assert member.isfile() and member.mtime==0
  assert t.extractfile(member).read()==(L/member.name).read_bytes()
r=json.loads((L/'fresh-replay/replay-receipt.json').read_text())
assert r['component_status']=='PASS' and not r['generated_partial_declarations']
assert r['endpoint']=='Cayley.literal_source_claim_false'
assert not list(L.rglob('*.olean'))
receipt={'status':'PASS','exact_inventory':True,'files_verified':len(actual),'original_bindings_verified':bound,
 'manifest_sha256':sha((L/'manifest.json').read_bytes()),'source_only_archive_sha256':sha((L/'source-only.tar.gz').read_bytes()),
 'formal_endpoint':r['endpoint'],'actual_declaration_count':r['actual_declaration_count'],
 'novelty':'HOLD','acceptance':'HOLD','accepted_credit':0,'counts':{'additional':9,'total':39,'next':40}}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
