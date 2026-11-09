from pathlib import Path
import json,hashlib,datetime,subprocess,sys
O=Path(__file__).parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((O/'finalmanifest.json').read_text());assert m['excludes_explicitly']==['finalmanifest.json','verification-receipt.json']
actual={str(p.relative_to(O)) for p in O.rglob('*') if p.is_file() and p.name not in m['excludes_explicitly']}
assert actual==set(m['files'])
for n,d in m['files'].items():assert h(O/n)==d,n
count=0
for fn in ['freeze.json','body-bindings.json','extra-bindings.json']:
 rows=json.loads((O/fn).read_text());rows=rows['scientific'] if isinstance(rows,dict) else rows
 for r in rows:
  assert h(Path(r['original']))==r['sha256'],r['original']
  assert h(Path(r['copy']))==r['sha256'],r['copy'];count+=1
hist=json.loads((O/'history-screen.json').read_text());assert not hist['mismatches']
for r in hist['verified_references']:assert h(Path(r['path']))==r['sha256']
for r in json.loads((O/'body-bindings.json').read_text()):
 p=Path(r['copy'])
 if p.suffix=='.pdf':assert h(O/'work'/p.name)==h(p)
for p in (O/'retrieved').glob('*.pdf'):assert h(p)==h(O/'work'/p.name)
r=subprocess.run([sys.executable,str(O/'checks.py')],capture_output=True,text=True,check=True)
assert json.loads(r.stdout)==json.loads((O/'check-results.json').read_text())
# Replay must not mutate any manifested byte.
for n,d in m['files'].items():assert h(O/n)==d,n
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','manifest_sha256':h(O/'finalmanifest.json'),'files':len(actual),'original_copy_bindings':count,'immutable_history_references':len(hist['verified_references']),'check_replay':json.loads(r.stdout),'limits':'hash/source/finite-control verification, not mathematical acceptance or global prior-art clearance; ledger/NEXT snapshot only'}
(O/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2))
