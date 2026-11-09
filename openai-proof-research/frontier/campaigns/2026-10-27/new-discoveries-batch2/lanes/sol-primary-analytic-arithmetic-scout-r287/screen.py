import runpy,re,json
from pathlib import Path
n=runpy.run_path(str(Path(__file__).with_name('work.py')));L=n['L'];h=n['h']
patterns={
'pochhammer':r'Pochhammer|Karp|Toeplitz determinant',
'hardy':r'backward shift|Karlovych|Shargorodsky',
'lattice':r'Two.cover Property|Gr.tzer|slim.*semimodular',
'charges':r'Maxwell.*(?:charge|equilibrium)|Rodrigues.*descendant',
'codes':r'complementary pairs|Li.{0,4}Shi.{0,4}Ling',
'tensor':r'Strassen|Salmon|Comon',
'integration':r'Novak|tractability|cubature',
}
rows=[];refs=[]
for p in sorted(Path('openai-proof-research/sources/cache').rglob('*.tex')):
 d=p.read_bytes();digest=h(d)
 # Freeze identity before decoding/reading; immutable references reused, no historical tree copying.
 refs.append({'path':str(p.resolve()),'sha256':digest,'bytes':len(d)})
 s=d.decode(errors='replace')
 for label,pat in patterns.items():
  hits=list(re.finditer(pat,s,re.I))
  if hits: rows.append({'family':label,'path':str(p.resolve()),'sha256':digest,'passages':[s[max(0,m.start()-200):m.start()+1000] for m in hits[:3]]})
 assert h(p.read_bytes())==digest
(L/'cache-references.json').write_text(json.dumps(refs,indent=2));(L/'semantic-hits.json').write_text(json.dumps(rows,indent=2))
print('files',len(refs),'hits',len(rows))
for r in rows:print(r['family'],r['path'],r['passages'][0][:450])
