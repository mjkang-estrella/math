from pathlib import Path
import hashlib,json,datetime
p=Path(__file__).resolve().parent
def sha(q): return hashlib.sha256(q.read_bytes()).hexdigest()
m=json.loads((p/'manifest.json').read_text())
excluded={'manifest.json','verification-receipt.json'}
assert set(m['excluded'])==excluded
actual={str(q.relative_to(p)) for q in p.rglob('*') if q.is_file() and str(q.relative_to(p)) not in excluded}
assert actual==set(m['files'])
for n,h in m['files'].items(): assert sha(p/n)==h,n
f=json.loads((p/'freeze-before.json').read_text())
for row in f['scientific']:
    assert sha(p/row['copy'])==row['sha256'],row['copy']
    assert sha(Path(row['original']))==row['sha256'],row['original']
assert json.loads((p/'independent-evidence.json').read_text())['status']=='PASS'
assert json.loads((p/'freeze-after.json').read_text())['unchanged']
r={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
   'manifest_sha256':sha(p/'manifest.json'),'verified_files':len(actual),
   'scientific_inputs_unchanged':True,'excluded':sorted(excluded),
   'limits':'Checks byte integrity and exact-check evidence; does not mechanically prove analytic reasoning or source interpretation.'}
(p/'verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
