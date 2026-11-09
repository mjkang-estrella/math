from pathlib import Path
import re
P=Path(__file__).resolve().parent
for name,pat in [('groupoid','separat|Conjecture'),('morita','counterexample|Theorem'),('matroids','counterexample|Theorem 1'),('codes','counterexample|Conjecture'),('zeros','Conjecture|Theorem 1'),('grid','Conjecture|alpha|α')]:
 t=(P/(name+'.txt')).read_text();print('\nSOURCE',name,'LENGTH',len(t))
 for m in list(re.finditer(pat,t,re.I))[:16]:print('OFFSET',m.start(),t[max(0,m.start()-180):m.end()+1100])
