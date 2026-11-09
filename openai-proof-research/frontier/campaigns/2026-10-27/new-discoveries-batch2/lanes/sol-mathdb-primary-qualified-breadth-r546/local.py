from pathlib import Path
import re,json
P=Path(__file__).resolve().parent;out=[]
for name,pat in [('morita',r'Lemma\s+1\.|Proof\.'),('codes',r'ounter.?example|onjecture'),('grid',r'\\alpha_\{m\}\([^=]{0,80}='),('zeros',r'Conjecture 1\.8|Theorem 1\.9')]:
 t=re.sub(r'\s+',' ',(P/(name+'.txt')).read_text());print('\n',name)
 ms=list(re.finditer(pat,t));ms=ms[:3] if name!='codes' else ms[-5:]
 for m in ms:
  s=t[max(0,m.start()-80):m.end()+2100];print(s);out.append({'source':name,'normalized_offset':m.start(),'text':s})
(P/'local-passages.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
