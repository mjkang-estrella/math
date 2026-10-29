from pathlib import Path
from bs4 import BeautifulSoup
P=Path(__file__).resolve().parent
for f in (P/'sources').glob('*-html.html'):
 s=BeautifulSoup(f.read_text(),'html.parser')
 for m in s.find_all('math'):m.replace_with(' $'+m.get('alttext','')+'$ ')
 for x in s.find_all(['script','style']):x.decompose()
 lines=[]
 for x in s.find_all(['p','h1','h2','h3','h4','h5','h6','figcaption','tr']):
  if x.find_parent(['p','tr']):continue
  lines.append(' '.join(x.get_text(' ',strip=True).split()))
 f.with_name(f.stem+'-compact.txt').write_text('\n'.join(lines))
