from pathlib import Path
import re,json
P=Path(__file__).resolve().parent;out=[]
for name,pat,count in [('morita',r'Theorem\s*\.|1 Proof',3),('codes',r'counter.?example|Example\s+6\.|Conjecture\s+6\.',5),('zeros',r'Conjecture\s+[12]\.|Theorem\s+1\.',5),('grid',r'alpha_\{m\}.*?=|k.*?resolving set',4)]:
 t=re.sub(r'\s+',' ',(P/(name+'.txt')).read_text());print('\n',name)
 for m in list(re.finditer(pat,t,re.I))[:count]:
  s=t[max(0,m.start()-100):m.end()+1800];print(s);out.append({'source':name,'normalised_offset':m.start(),'text':s})
(P/'detail-passages.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
