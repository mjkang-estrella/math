from fetch import get,D
import json
items=[('edge-thesis-2023.pdf','https://theses.hal.science/tel-04259639/document'),('edge-successor-2021.pdf','https://arxiv.org/pdf/2109.15215')]
o=json.loads((D/'sources/edge-citers.json').read_text())
for w in o['results']:
 if w.get('publication_year')==2025:
  p=(w.get('best_oa_location') or {}).get('pdf_url')
  if p:items.append(('random-independent-2025.pdf',p))
for x in items:print(get(x),flush=True)
