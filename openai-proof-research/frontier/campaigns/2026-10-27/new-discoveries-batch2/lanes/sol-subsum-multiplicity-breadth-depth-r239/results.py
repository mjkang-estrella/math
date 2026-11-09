from pathlib import Path
import re,html
L=Path(__file__).parent
for p in (L/'primary').glob('*search.html'):
 s=p.read_text(); print('\n',p.name)
 for block in re.split(r'<li class="arxiv-result',s)[1:11]:
  ids=re.findall(r'https://arxiv.org/abs/[^"<]+',block)
  title=re.search(r'<p class="title[^>]*>(.*?)</p>',block,re.S)
  print(ids[:1], re.sub('<[^>]*>','',title[1]).strip() if title else '')
