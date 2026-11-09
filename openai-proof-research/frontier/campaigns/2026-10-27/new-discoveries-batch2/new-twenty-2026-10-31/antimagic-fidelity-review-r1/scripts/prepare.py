from pathlib import Path
import re
L=Path(__file__).resolve().parents[1]; d=L/'fresh'; mods={p.stem:p for p in d.glob('*.lean')}; done=set(); order=[]
def visit(m):
 if m in done:return
 done.add(m)
 for x in re.findall(r'^import\s+(\S+)',mods[m].read_text(),re.M):
  if x in mods:visit(x)
 order.append(m)
for m in sorted(mods):visit(m)
(L/'evidence/order.txt').write_text('\n'.join(order)+'\n')
