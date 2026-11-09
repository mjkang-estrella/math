from pathlib import Path
import json,re,html
D=Path(__file__).resolve().parents[1]
for n in ['holroyd-index','author-chung','hurlbert-pubs']:
 s=(D/'downloads'/n/'body-0').read_text()
 if n=='holroyd-index':print(n,re.findall(r'href\s*=\s*["\']([^"\']+)["\']',s,re.I))
 text=html.unescape(re.sub('<[^>]+>',' ',s));text=re.sub(r'\s+',' ',text)
 (D/'downloads'/n/'text.txt').write_text(text)
 for m in re.finditer('universal|thesis|dissert',text,re.I):
  if n!='holroyd-index':print(n,text[max(0,m.start()-100):m.start()+180])
p=json.loads((D/'downloads/pool-head/body-0').read_text());print('POOL HEAD',p['sha'])
t=json.loads((D/'downloads/pool-tree/body-0').read_text());print('truncated',t.get('truncated'),'paths',len(t.get('tree',[])))
print('pool matches',[x['path'] for x in t['tree'] if re.search('hurlbert|ucycle|universal.?cycle',x['path'],re.I)])
print('github',json.loads((D/'downloads/github-one/body-0').read_text()).get('total_count'))
