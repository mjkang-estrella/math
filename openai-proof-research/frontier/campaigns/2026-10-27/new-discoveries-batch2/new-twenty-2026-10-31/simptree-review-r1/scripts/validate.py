import json,pathlib,hashlib
L=pathlib.Path(__file__).resolve().parents[1]
r=json.loads((L/'review.json').read_text());m=json.loads((L/'evidence/math.json').read_text())
for k,v in m['circuits'].items():
 actual=sum(v['by_length'].values());claimed=r['gates']['B']['circuit_counts_by_m'][k]
 assert actual==claimed,(k,actual,claimed)
assert m['f_vector']==[12,30,29,9]
assert not m['complete_order_exists']
assert not m['circuits']['2']['by_length']
assert (L/'evidence/inputs-before.sha256').read_bytes()==(L/'evidence/inputs-after.sha256').read_bytes()
assert hashlib.sha256((L/'evidence/inputs-before.sha256').read_bytes()).hexdigest()==r['integrity']['before_manifest_sha256']
print('Review JSON, circuit totals, count claims, ordering claim and manifest identity: PASS')
