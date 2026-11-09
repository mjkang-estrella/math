from pathlib import Path
import json,subprocess,hashlib
L=Path(__file__).resolve().parent
for name in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((L/'administrative'/name).read_text());print(name,'fully parsed',len(d),'top-level fields')
rows=[]
for lane,pdf,txt in [('sol-super-coupon-source-prior-breadth-r2','frozen-live/'+n+'.pdf','texts/'+n+'.txt') for n in ['target-vor','target-correction','aldous-book','dense-cover']]+[('sol-wide-analytic-source-scout-r254','primary/1202.3900v1.pdf','texts/1202.3900v1.txt')]:
 base=L/'frozen/lanes'/lane
 out=subprocess.check_output(['pdftotext','-layout',str(base/pdf),'-'])
 expected=(base/txt).read_bytes()
 rows.append(dict(pdf=str((base/pdf).relative_to(L)),text=str((base/txt).relative_to(L)),sha256=hashlib.sha256((base/pdf).read_bytes()).hexdigest(),fresh_text_matches=out==expected))
(L/'extraction-check.json').write_text(json.dumps(rows,indent=2))
print(json.dumps(rows,indent=2))
