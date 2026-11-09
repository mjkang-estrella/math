from pathlib import Path
import json
D=Path(__file__).resolve().parents[1]
for name in ['openalex-source-doi','openalex-chung-search','github-two']:
 p=D/'downloads'/name/'body-0'
 if not p.exists():continue
 try:j=json.loads(p.read_text())
 except Exception:continue
 print(name)
 for x in j.get('results',[j]):print({k:x.get(k) for k in ['id','display_name','doi','cited_by_count','cited_by_api_url','open_access','primary_location','total_count']})
 if name=='github-two': print([(x['full_name'],x.get('description')) for x in j.get('items',[])])
