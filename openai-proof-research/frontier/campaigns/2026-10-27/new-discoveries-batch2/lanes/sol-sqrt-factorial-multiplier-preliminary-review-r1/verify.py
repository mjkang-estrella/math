from pathlib import Path
import hashlib,json,datetime
p=Path(__file__).resolve().parent
digest=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
manifest=json.loads((p/'final-manifest.json').read_text())
actual={str(f.relative_to(p)) for f in p.rglob('*') if f.is_file() and f.name not in manifest['excludes']}
assert actual==set(manifest['files'])
for name,h in manifest['files'].items(): assert digest(p/name)==h,name
rows=json.loads((p/'freeze.json').read_text())
for r in rows:
    assert digest(Path(r['original']))==digest(Path(r['copy']))==r['sha256_before']==r['sha256_after_review']
for f in (p/'retrieval').glob('*.receipt.json'):
    r=json.loads(f.read_text())
    if 'sha256' in r:
        prefix=f.name.removesuffix('.receipt.json')
        target=p/'retrieval'/(prefix+'.json' if prefix in ['crossref','openalex'] else prefix+'.body')
        assert digest(target)==r['sha256']
receipt={'status':'PASS','time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'manifest_sha256':digest(p/'final-manifest.json'),'files_verified':len(actual),
         'original_copy_pairs_verified':len(rows),'separate_guarded_verification_after_final_writes':True,
         'math_status':'ordinary proof review only; no Lean or acceptance',
         'resource_envelope':'guard AS/groupRSS512MiB CPU210 wall230; no cap raises'}
(p/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
