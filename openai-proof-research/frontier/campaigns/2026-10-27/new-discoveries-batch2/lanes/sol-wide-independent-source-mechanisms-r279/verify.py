import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((L/'MANIFEST.json').read_text())
assert 'MANIFEST.json' not in manifest and 'verification-receipt.json' not in manifest
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['MANIFEST.json','verification-receipt.json']}
assert actual==set(manifest)
for name,h in manifest.items():assert sha(L/name)==h,name
refs=[]
for name in ['question-bindings.json','proof-bindings.json','semantic-search-inventory.json']:
 refs+=json.loads((L/name).read_text())
refs += [json.loads(s) for s in (L/'bindings.jsonl').read_text().splitlines()]
changes=[]
for q in refs:
 p=pathlib.Path(q['path'])
 if sha(p)!=q['sha256']:changes.append(str(p))
# Report changing external admin/history honestly; never silently certify it immutable.
primary=json.loads((L/'primary-access.json').read_text())
for q in primary:
 if 'path' not in q:continue
 p=pathlib.Path(q['path']);assert sha(p)==q['sha256'];assert sha(p.with_suffix('.txt'))==q['text_sha256']
for n in ['access-zeckendorf.pdf.json','access-zeckendorf-current.html.json']:
 q=json.loads((L/n).read_text());p=pathlib.Path(q['path']);assert sha(p)==q['sha256']
 if 'text_sha256' in q:assert sha(p.with_suffix('.txt'))==q['text_sha256']
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS' if not changes else 'FAIL: external references changed','manifest_sha256':sha(L/'MANIFEST.json'),'payload_files':len(manifest),'external_reference_checks':len(refs),'changed_external_references':changes,'scope':'integrity verification, not a mathematical proof or novelty certification','separate_guarded_verification':True}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt));assert not changes
