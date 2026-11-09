from pathlib import Path
import re,json
P=Path(__file__).resolve().parent;t=re.sub(r'\s+',' ',(P/'matrix.txt').read_text());out=[]
for m in list(re.finditer(r'Theorem\s+1\.|Theorem\s+1 |Main result',t))[:3]:
 s=t[max(0,m.start()-100):m.end()+2500];print(s);out.append({'source':'matrix','normalized_offset':m.start(),'text':s})
print('CODES HEADER',re.sub(r'\s+',' ',(P/'codes.txt').read_text())[3500:6500])
(P/'matrix-passages.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
