from pathlib import Path
import json,re
D=Path(__file__).resolve().parents[1]
j=json.loads((D/'downloads/openalex-chung-citers/body-0').read_text());rows=j.get('results',[])
lines=[f"OpenAlex total {j.get('meta',{}).get('count')}; returned {len(rows)}"]
for x in rows:
 lines.append(f"{x['id']} | {x['publication_date']} | {x['title']} | {x.get('doi')}")
(D/'citation-title-screen.txt').write_text('\n'.join(lines)+'\n')
print(lines[0])
for x in rows:
 if re.search('permut|graph universal|gray code|pattern',x['title'],re.I):
  print(x['id'],x['title'],x.get('doi'))
  print([z.get('pdf_url') for z in x.get('locations',[]) if z.get('pdf_url')])
p=D/'downloads/jackson-openalex/body-0'
if p.exists():
 x=json.loads(p.read_text());print('JACKSON LOCATIONS',x.get('locations'))
