import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parents[1];r=json.loads((L/'results.json').read_text());wanted=json.loads((L/'reservation.json').read_text())['ids']
assert len(r)==20 and set(map(int,r))==set(wanted)
for i,v in r.items():
 b=(L/'sources'/f'{i}.raw.jsonl').read_bytes();assert b.endswith(b'\n');assert hashlib.sha256(b).hexdigest()==v['provenance']['raw_sha256']
 assert hashlib.sha256(v['literal_statement'].encode()).hexdigest()==v['statement_sha256'];assert not v['accepted']
assert (L/'SUMMARY.md').exists() and (L/'lean/Delta153.olean').exists() and (L/'lean/Soundness.olean').exists()
assert not (L/'lean/PureCheck.olean').exists()
print('PASS 20 reserved keys, exact raw/statement hashes, zero acceptances, required report, two compiled partial modules, no incomplete computation artifact')
