import pathlib,json,re,hashlib
L=pathlib.Path(__file__).resolve().parents[1]
p=L/'SUMMARY.md';s=p.read_text()
for word in ['order','orders','variables','all','Theorem','Theorems','Proposition','Propositions','Corollary','Conjecture','Lemma','Remark','Section','through','of','in','CPUs','wall','CPU','above','after','to','and','first','plus','Stanton','Alon']:
 s=re.sub(r'\b'+word+r'(?=\d)',word+' ',s)
s=re.sub(r'(?<=\d)(?=(?:s,|s\.|GiB|cases|paths|masks|systems|mismatches|exact|completed|cubic|quartic|of)\b)',' ',s)
p.write_text(s)
r=json.loads((L/'results.json').read_text());assert len(r)==20
reserved=json.loads((L/'reservation.json').read_text())['ids'];assert set(r)==set(map(str,reserved))
for i,x in r.items():
 b=(L/f'sources/{i}.raw.jsonl').read_bytes();assert b.endswith(b'\n')
 assert hashlib.sha256(b).hexdigest()==x['provenance']['raw_sha256']
 assert hashlib.sha256((L/x['source']['pdf']).read_bytes()).hexdigest()==x['source']['pdf_sha256']
 assert x['lean_endpoint'] is None and x['accepted_credit']==0
print('PASS: exact 20 keys, reserved IDs, newline-preserved raws, raw/PDF hashes, zero credit and no surrogate Lean endpoint.')
