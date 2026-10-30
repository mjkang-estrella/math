from pathlib import Path
import json,importlib.util
L=Path(__file__).resolve().parent;B=L.parent
print('dulwich',importlib.util.find_spec('dulwich'))
for r in [138,139,140]:
 p=B/f'sol-fresh-source-discovery-r{r}'/'registry-delta-receipt.json';d=json.loads(p.read_text());print(r,{k:v for k,v in d.items() if k!='paths'})
d=json.loads((B/'sol-steiner-gp-source-prior-review-r2/retrieved/source-citations.json').read_text())
out=[]
for x in d['results']:
 inv=x.get('abstract_inverted_index') or {}; a={i:w for w,ids in inv.items() for i in ids}; abstract=' '.join(a[i] for i in sorted(a))
 out.append({'id':x['id'],'title':x['title'],'doi':x['doi'],'abstract':abstract,'locations':[(z.get('landing_page_url'),z.get('pdf_url')) for z in x['locations']]})
(L/'citation-abstracts.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
