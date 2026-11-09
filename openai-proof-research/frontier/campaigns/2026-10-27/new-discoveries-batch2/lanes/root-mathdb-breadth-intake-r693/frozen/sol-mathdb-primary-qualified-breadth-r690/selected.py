import pathlib,json,hashlib,re
P=pathlib.Path(__file__).resolve().parent
for l in (P/'derivative-bindings.jsonl').read_text().splitlines():
 e=json.loads(l);b=(P/e['path']).read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
t=(P/'335423.txt').read_text()
print('335423 proof locations',[(m.start(),t[max(0,m.start()-200):m.start()+1000]) for m in re.finditer('coprime|Bézout|Bezout|polynomials.*?integer',t,re.I)][:8])
print('406505 selected full subsection 3.1:',(P/'406505.txt').read_text()[15000:20950])
