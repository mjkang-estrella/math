from pathlib import Path
from bs4 import BeautifulSoup
P=Path(__file__).resolve().parent
for name in ['kunisky','mulgund','transport']:
 s=BeautifulSoup((P/'sources'/f'{name}.html').read_text(),'html.parser')
 for x in s.select('math'):x.replace_with(x.get('alttext',x.get_text()))
 (P/'sources'/f'{name}.txt').write_text(s.get_text(' ',strip=True))
