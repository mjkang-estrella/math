import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'final-manifest.json').read_text());assert set(m['excludes'])=={'final-manifest.json','final-verification.json'}
for r in m['files']:
 p=L/r['path'];assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],r['path']
assert {r['path'] for r in m['files']}=={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in m['excludes']}
for b in json.loads((L/'bindings.json').read_text()):
 assert sha(pathlib.Path(b['original']))==b['sha256']
 if 'copy'in b:assert sha(pathlib.Path(b['copy']))==b['sha256']
for name in ['math-verification.json','exhaustive-verification.json','zero-verification.json']:
 assert json.loads((L/name).read_text())['pass']
assert json.loads((L/'G-zero-result.json').read_text())['witness'] is None
assert len(json.loads((L/'two-defect-witness.json').read_text())['abnormal_edges'])==2
out={'pass':True,'utc':str(datetime.datetime.now(datetime.timezone.utc)),'manifest_sha256':sha(L/'final-manifest.json'),'verified_files':len(m['files']),'original_copy_bindings_unchanged':True,'separate_guarded_verifier':True,'excluded_self_and_receipt':True,'status':'RETIRE exact publicly resolved target; no credit'}
(L/'final-verification.json').write_text(json.dumps(out,indent=2));print(out)
