from research import *
import re,html
for pat in ['bing-tmna.html','search-tmna.html']:
 p=next((L/'frozen').glob('*/'+pat));s=p.read_text();print(pat,html.unescape(re.sub('<[^>]+>',' ',s))[-18000:])
print(fetch('https://arxiv.org/search/?query=%22On+the+operator+of+center%22&searchtype=all','arxiv-exact.html'))
print(fetch('https://apcz.umk.pl/TMNA/article/view/47721/37304','tmna-preview.html'))
