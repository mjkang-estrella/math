from pathlib import Path
import re,html,json
L=Path(__file__).parent
for name in ['atomic-citers.html','uniqueness-search.html','bk-search.html']:
 p=L/'primary'/name
 if not p.exists():continue
 print(name)
 for block in re.split(r'<li class="arxiv-result',p.read_text())[1:]:
  ids=re.findall(r'https://arxiv.org/abs/[^"<]+',block)
  title=re.search(r'<p class="title[^>]*>(.*?)</p>',block,re.S)
  print(ids[:1],html.unescape(re.sub('<[^>]*>','',title[1])).strip() if title else '')
print('HISTORY')
for k,v in json.loads((L/'history-hits.json').read_text()).items():
 print(k,[(Path(x['path']).parent.name,x['excerpt']) for x in v[:4]])
