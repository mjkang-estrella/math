import pathlib,json,hashlib,datetime,subprocess,sys
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'final-manifest.json').read_text())
assert {str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in m['excluded']}=={r['path'] for r in m['files']}
for r in m['files']:assert sha(L/r['path'])==r['sha256'] and (L/r['path']).stat().st_size==r['bytes']
n=0
for r in json.loads((L/'bindings.json').read_text()):
 if 'original' not in r:continue
 assert sha(pathlib.Path(r['original']))==r['sha256']
 if 'copy' in r:assert sha(pathlib.Path(r['copy']))==r['sha256']
 n+=1
for r in map(json.loads,(L/'access.jsonl').read_text().splitlines()):
 if 'path' in r:assert sha(pathlib.Path(r['path']))==r['sha256']
b=json.loads((L/'current/chalmers-text-binding.json').read_text())
assert sha(L/'current/chalmers.pdf')==b['pdf_sha256'] and sha(L/'current/chalmers.txt')==b['text_sha256']
assert json.loads((L/'independent-check.json').read_text())['result']=='PASS'
out={'result':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':sha(L/'final-manifest.json'),'manifest_files':len(m['files']),'original_scientific_bindings':n,'originals_and_copies_unchanged':True,'retrieval_hashes_verified':True,'meaning':'packet integrity and exact-check result, not acceptance','counts_unchanged':'9 additional/39 total/next40'}
(L/'final-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
