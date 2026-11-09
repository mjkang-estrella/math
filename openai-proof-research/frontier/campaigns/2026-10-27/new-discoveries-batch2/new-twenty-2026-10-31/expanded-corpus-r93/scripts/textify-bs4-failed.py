from pathlib import Path
from bs4 import BeautifulSoup
import json
D=Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('*.html'):
 s=BeautifulSoup(p.read_text(),'html.parser')
 for t in s(['script','style','annotation']):t.decompose()
 text=s.get_text(' ',strip=True)
 (D/'sources'/p.with_suffix('.txt').name).write_text(text)
 for tag in s.select('.ltx_theorem'):
  t=tag.get_text(' ',strip=True)
  if 'conjecture' in t.lower():print(p.name,tag.get('id'),t[:7000])
for f in ['openai-head.json','omega-head.json']:
 o=json.loads((D/'sources'/f).read_text());print(f,o['sha'],o['commit']['committer']['date'],o['commit']['tree'])
