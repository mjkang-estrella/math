from pathlib import Path
import json,hashlib
P=Path(__file__).resolve().parent
r=json.loads((P/'check-results.json').read_text())
assert len(r['factors'])==30 and len(r['pairs'])==234
assert sum('subsets'in x for x in r['pairs'])==42
assert sum(x.get('subsets',0) for x in r['pairs'])==5503420
assert not any(x.get('counterexample') is not None for x in r['pairs'])
for f in r['factors']:
 a=f['adj'];assert all(not(a[i]>>i&1) for i in range(len(a)))
 assert all((a[i]>>j&1)==(a[j]>>i&1) for i in range(len(a)) for j in range(len(a)))
for l in (P/'sourcebytes.sha256').read_text().splitlines():
 h,f=l.split('  ',1);assert hashlib.sha256((P/f).read_bytes()).hexdigest()==h,f
print('PASS: exact result inventory and frozen source-byte hashes')
