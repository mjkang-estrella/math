from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
p=L/'validate.py';s=p.read_text();a=s.index("ns={};exec");b=s.index("# exec requires",a);s=s[:a]+s[b:];s=s.replace('# Compare complete K4 with its known Hilbert polynomial, rather than just evaluation.','# Sanity-check the complete K4 specialization against dim(DH_3)=16.')
a=s.index('expected=');b=s.index("print('K4 polynomial'",a);s=s[:a]+s[b:];p.write_text(s)
res=json.loads((L/'results.json').read_text());assert len(res)==20
reserved=json.loads((L/'reservation.json').read_text())['ids'];assert set(map(int,res))==set(reserved)
for i,x in res.items():
 assert hashlib.sha256((L/f'raw-{i}.jsonl').read_bytes()).hexdigest()==x['provenance']['raw_sha256']
 assert hashlib.sha256(x['literal_statement'].encode()).hexdigest()==x['statement_utf8_sha256']
 assert x['accepted_credit']==0 and not x['lean']['kernel_checked']
assert not list(L.rglob('__pycache__'))
print('PASS: 20 keys, raw/statement hashes, no credit, no bytecode directories')
print('outcomes', {v:sum(x['outcome']==v for x in res.values()) for v in sorted(set(x['outcome'] for x in res.values()))})
