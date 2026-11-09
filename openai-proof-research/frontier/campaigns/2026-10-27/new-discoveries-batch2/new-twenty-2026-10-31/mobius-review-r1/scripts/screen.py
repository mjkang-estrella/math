from pathlib import Path
import json
D=Path(__file__).resolve().parents[1]
w=json.loads((D/'downloads/citing/body').read_text()); print('citing total',w['meta']['count'])
for x in w['results']:
 print(x['id'],x['publication_year'],x['title'],x.get('doi'));print('  ',[(l.get('pdf_url'),l.get('landing_page_url')) for l in x['locations'] if l.get('is_oa')][:3])
t=json.loads((D/'downloads/pool-tree/body').read_text());print('pool truncated',t.get('truncated'))
for x in t['tree']:
 if x['path'].startswith('candidates/') or x['path'].endswith(('projects.yml','projects.yaml')): print(x['path'])
