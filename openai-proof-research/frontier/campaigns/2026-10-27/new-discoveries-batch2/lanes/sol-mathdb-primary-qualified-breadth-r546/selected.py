from pathlib import Path
import re,json
P=Path(__file__).resolve().parent;out=[]
for name,pat in [('groupoid',r'Conjecture'),('morita',r'Theorem|Example'),('matroids',r'Theorem 1\.|counterexample'),('codes',r'Example 6|counterexample'),('zeros',r'Conjecture|Theorem 1'),('grid',r'Conjecture|alpha_\{m\}')]:
 t=(P/(name+'.txt')).read_text();print('\nSOURCE',name)
 matches=list(re.finditer(pat,t,re.I));matches=matches[-3:] if name in ['groupoid','grid','codes'] else matches[:3]
 for m in matches:
  s=t[max(0,m.start()-100):m.end()+2200];print('OFFSET',m.start(),re.sub(r'\s+',' ',s));out.append({'source':name,'start':max(0,m.start()-100),'end':m.end()+2200,'text':s})
(P/'selected-passages.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
