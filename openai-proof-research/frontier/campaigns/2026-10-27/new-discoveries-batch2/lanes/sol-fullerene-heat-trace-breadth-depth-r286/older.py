from pathlib import Path
import sys,runpy,re
L=Path(__file__).resolve().parent;sys.argv=['work','freeze',str(L/'primary/older-search.html')];ns=runpy.run_path(str(L/'work.py'));s=ns['freeze'](L/'primary/older-search.html').read_text()
for b in s.split('<li class="arxiv-result">')[1:]:
 a=re.search(r'arxiv.org/abs/([^"<]+)',b);t=re.search(r'<p class="title is-5 mathjax">(.*?)</p>',b,re.S)
 if a and t:print(a.group(1),re.sub('<[^>]+>','',t.group(1)).strip())
