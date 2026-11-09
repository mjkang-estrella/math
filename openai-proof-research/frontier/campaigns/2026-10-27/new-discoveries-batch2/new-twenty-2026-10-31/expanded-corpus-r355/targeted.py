exec(compile((__import__('pathlib').Path(__file__).parent/'research.py').read_text(),'research.py','exec'))
import re
for key,terms in [('7af89af8c8e6efb0',['Submitted','v1','v2','journal-ref','doi']),('6ba6dc2024d1c0d2',['Submitted','v1','v2','v3','journal-ref','doi']),('5fc57b80f25fe40e',['Submitted','v1','v2','journal-ref','doi']),('14429a70095c21a0',['Submitted','v1','v2','v3','journal-ref','doi']),('9d1ecc704dc0c460',['Conjecture','minimally completable','bicoloring']),('b3286cf6067b72a8',['Conjecture','incidence algebra']),('cfa9ea11beb6462a',['Conjecture','3-partite'])]:
 p=P/'sources'/(key+'.txt'); lines=p.read_text().splitlines(); seen=set(); spans=[]; print('SOURCE',key)
 for n,s in enumerate(lines):
  if any(t in s for t in terms):
   a=max(0,n-2); b=min(len(lines),n+9); spans.append([a+1,b])
   for j in range(a,b):
    if j not in seen: print(str(j+1)+': '+lines[j]); seen.add(j)
 js('targeted-'+key+'.json',dict(path=str(p.relative_to(P)),sha256=sha(p.read_bytes()),spans=spans))
