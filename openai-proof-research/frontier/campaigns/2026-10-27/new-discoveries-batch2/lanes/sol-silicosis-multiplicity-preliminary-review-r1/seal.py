from pathlib import Path
import hashlib,json,datetime
O=Path(__file__).resolve().parent;B=O.parents[1]
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b)
 return h.hexdigest()
f=B/'lanes/root-silicosis-review-freeze-r1/review-freeze.json';m=json.loads(f.read_text());rows=[]
for n,h in m['files'].items():
 s=digest(Path(m['source_lane'])/n);c=digest(O/'frozen'/n);assert s==c==h
 rows.append(dict(path=n,expected=h,source=s,copy=c))
(O/'freeze-after.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=digest(f),all_38_unchanged=True,files=rows),indent=2))
searches=['"Modelling Silicosis" "Structure of Equilibria" Cambridge','"Pinelis" "silicosis"','rational product basis Descartes rule variation diminishing positive coefficients products x d','"Modelling silicosis: structure of equilibria" site:cambridge.org','Pinelis "L’Hospital rules for monotonicity" "Wilker" pdf','"rational" "Descartes systems" positive poles','"silicosis" "variation diminishing"','total positivity variation diminishing theorem Schoenberg bidiagonal pdf theorem','"rational" "product" "Descartes" "basis" total positivity','"silicosis" "1901.10670" multiplicity power law proof','"infinite" "rational" "products" "variation-diminishing" equilibria']
(O/'search-notes.json').write_text(json.dumps(dict(date_utc='2026-10-29',queries=searches,result='No exact full power-law resolution located; primary bodies and complete reduction discussed in review.md',failure=dict(url='https://sites.stat.washington.edu/jaw/COURSES/580s/581/HO/Schoenberg-50.ASMATHSzeged.pdf',tool='web open',message='(400) Timeout fetching',retried=False)),indent=2))
files={str(p.relative_to(O)):digest(p) for p in sorted(O.rglob('*')) if p.is_file() and p.name not in ['evidence-manifest.json','seal.log']}
(O/'evidence-manifest.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=files),indent=2))
print(json.dumps(dict(frozen_count=len(rows),unchanged=True,artifacts=len(files),review_sha256=digest(O/'review.md'))))
