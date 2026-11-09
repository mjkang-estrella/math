from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
checks=[]
for r in json.loads((L/'freeze.json').read_text()):
 assert sha(Path(r['original']))==r['sha256'],r['original']
 if 'copy' in r:assert sha(L/r['copy'])==r['sha256']
 checks.append(r['original'])
for r in json.loads((L/'provenance.json').read_text())['administrative_snapshots']:
 assert sha(L/r['file'])==r['sha256']
for p in (L/'access').glob('*.receipt.json'):
 r=json.loads(p.read_text())
 if 'file' in r:assert sha(L/r['file'])==r['sha256']
coverage=json.loads((L/'exactcoverage.json').read_text())
for r in coverage['bodies']:
 for k in ['body','extraction']:
  if k in r:assert sha(L/r[k]['file'])==r[k]['sha256']
manifest=json.loads((L/'manifest.json').read_text())
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
assert actual==set(manifest['files'])
for p,h in manifest['files'].items():assert sha(L/p)==h,p
assert (L/'access/springer.pdf').read_bytes().startswith(b'%PDF-')
s=(L/'access/springer.txt').read_text()
assert 'Question 3 For the triangular array' in s and 'Question 4 Does there exist' in s
assert '22 February 2025' in (L/'access/springer.html').read_text()
r={'status':'PASS','verified_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'original_bindings_verified':len(checks),'manifest_files_verified':len(actual),'manifest_sha256':sha(L/'manifest.json'),'checks':['originals and copies/references unchanged before/after','administrative snapshots','retrieval byte hashes','body and extraction hashes','manifest exact file set and every hash','published target/chronology anchors'],'limits':{'AS_bytes':536870912,'group_RSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230},'scientific_scope':'integrity and binding verification; not a mathematical proof or global novelty certificate'}
(L/'verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
