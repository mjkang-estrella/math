from pathlib import Path
import re,json
L=Path(__file__).resolve().parent
for name,start,end in [('correction','Abstract','References'),('arxiv-v2','6 Open question','Acknowledg'),('journal','6 Open question','Change history'),('rarity','Abstract','1 Introduction')]:
 s=(L/'sources'/f'{name}.txt').read_text();a=s.rfind(start);b=s.find(end,a+len(start));print(name,a,b,s[a:b if b>a else a+4500] if a>=0 else s[:6500])
j=json.loads((L/'registry-path-screen.json').read_text())
for d in j:
 print(d['path'],len(d['matches']))
 print('\n'.join(x for x in d['matches'] if re.search('numerical|2308[.]09500|Rosas.Ribeiro|infinite.chain|InfiniteChain',x.split('\t')[-1],re.I)))
