from pathlib import Path
import json
D=Path(__file__).resolve().parents[1]
for name in ['openalex-source-citers','openalex-chung-correct']:
 try:j=json.loads((D/'downloads'/name/'body-0').read_text())
 except Exception:continue
 print(name,j.get('meta'))
 for x in j.get('results',[j]):
  print({k:x.get(k) for k in ['id','title','doi','cited_by_count','publication_date']})
