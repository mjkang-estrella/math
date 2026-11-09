from research import *
import re,html
p=next((L/'frozen').glob('*/bing-tmna.html'));s=p.read_text();s=re.sub(r'<(script|style)\b.*?</\1>','',s,flags=re.S);print(html.unescape(re.sub('<[^>]+>',' ',s))[:15000])
p=next((L/'frozen').glob('*/tmna-preview.html'));out=L/'primary'/'tmna-preview.txt';subprocess.run(['pdftotext','-layout',str(p),str(out)],check=True);freeze(out);print(out.read_text())
print(fetch('https://arxiv.org/search/?query=%22center+of+distances%22+AND+Bartoszewicz&searchtype=all','arxiv-authors.html'))
