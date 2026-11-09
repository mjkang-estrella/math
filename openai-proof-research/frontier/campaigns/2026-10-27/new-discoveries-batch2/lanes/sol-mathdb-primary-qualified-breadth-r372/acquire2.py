from pathlib import Path
import json,re
L=Path(__file__).parent
s=(L/'acquire.py').read_text();s=s.replace("rows=[]","rows=json.loads((L/'sources.json').read_text())")
a=s.index('jobs=');z=s.index('\nrows=',a)
jobs=[]
for n in ['cover-shift','toric','simplex','polygon']:
 h=(L/'sources'/(n+'-original.html')).read_text();u=re.findall(r'https://content.ems.press/[^"\s<>]+\.pdf',h)[0];jobs.append((n+'-body',u))
jobs += [('simplex-successor','https://arxiv.org/pdf/1612.01893v1'),('toric-successor','https://mast.queensu.ca/~ggsmith/Papers/diRoccoJabbuschSmith.pdf'),('cover-successor','https://real.mtak.hu/15290/1/surveyfinal.pdf')]
s=s[:a]+'jobs='+repr(jobs)+s[z:];exec(compile(s,str(L/'acquire.py'),'exec'))
