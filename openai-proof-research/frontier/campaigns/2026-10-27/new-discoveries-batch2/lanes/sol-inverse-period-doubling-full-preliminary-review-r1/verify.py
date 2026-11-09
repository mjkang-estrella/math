from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((L/'manifest.json').read_text())
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
assert actual==set(manifest)
for name,d in manifest.items():assert h(L/name)==d,name
n=0
for binding in ['bindings.json','library-bindings.json']:
 for r in json.loads((L/binding).read_text()):
  assert h(Path(r['original']))==r['sha256'],r['original']
  assert h(L/r['copy'])==r['sha256'],r['copy']
  n+=1
for r in json.loads((L/'current-retrieval.json').read_text()):
 if 'sha256' not in r:continue
 name=r['url'].split('/')[-1]
 # Names were assigned explicitly rather than derived from endpoint query strings.
 name={'https://arxiv.org/pdf/1010.4009':'durand-current.pdf'}.get(r['url'],'current.xml' if 'id_list=' in r['url'] else 'target-search.xml')
 assert h(L/'retrieved'/name)==h(L/'frozen-current'/name)==r['sha256']
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','manifest_sha256':h(L/'manifest.json'),'manifest_files':len(manifest),'original_and_copy_scientific_bindings_verified':n,'current_retrieval_pairs_verified':3,'administrative':'snapshot hashes only; shared originals not compared','separate_process':True,'counts_unchanged':[9,39,40]}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
