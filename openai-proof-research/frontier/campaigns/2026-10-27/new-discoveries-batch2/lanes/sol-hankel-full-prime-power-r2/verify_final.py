from pathlib import Path
import hashlib,json,datetime
p=Path(__file__).resolve().parent
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
errors=[];original_count=0;retrieved_count=0
bindings=json.loads((p/'input-bindings.json').read_text())
for x in bindings['scientific_inputs']:
    for q in [Path(x['original']),p/x['copy']]:
        if not q.is_file() or sha(q)!=x['sha256']:errors.append('assigned binding: '+str(q))
    original_count+=1
for x in json.loads((p/'retrieved-freeze.json').read_text())['bindings']:
    for q in [p/x['original'],p/x['copy']]:
        if not q.is_file() or sha(q)!=x['sha256']:errors.append('retrieved binding: '+str(q))
    retrieved_count+=1
manifest=json.loads((p/'manifest.json').read_text())
excluded=['manifest.json','verification-receipt.json']
if manifest['excluded']!=excluded:errors.append('wrong exclusions')
actual={str(q.relative_to(p)) for q in p.rglob('*') if q.is_file() and str(q.relative_to(p)) not in excluded}
if actual!=set(manifest['files']):errors.append('manifest file-set mismatch')
for rel,h in manifest['files'].items():
    q=p/rel
    if not q.is_file() or sha(q)!=h:errors.append('manifest hash: '+rel)
if json.loads((p/'check-results.json').read_text())['status']!='PASS':errors.append('checks failed')
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS' if not errors else 'FAIL','manifest_sha256':sha(p/'manifest.json'),'manifest_files':len(actual),'assigned_original_copy_pairs':original_count,'retrieved_original_copy_pairs':retrieved_count,'administrative_originals_bound':False,'excluded':excluded,'errors':errors,'scope':'Hashes and finite control status only; not a proof checker or novelty certificate. Separate guarded verification after final writes.'}
(p/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
if errors:raise SystemExit(1)
