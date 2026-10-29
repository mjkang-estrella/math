from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent
for name in ['manifest.sha256','sourcebytes.sha256']:
 lines=(P/name).read_text().splitlines()
 for line in lines:
  h,fn=line.split('  ',1)
  assert hashlib.sha256((P/fn).read_bytes()).hexdigest()==h,fn
 print(name,len(lines),'PASS')
a=json.loads((P/'check-results.json').read_text());b=json.loads((P/'route-results.json').read_text())
assert a['distinct_U_counts']==[1,2,2,4,6,11,18,33,59]
assert b['cone_obstruction']['output'][2]==[9,38,20,12]
assert len(b['finite_field_checks'])==18
assert not (P/'PROOF.md').exists()
print('exact reports PASS; source result remains unresolved')
