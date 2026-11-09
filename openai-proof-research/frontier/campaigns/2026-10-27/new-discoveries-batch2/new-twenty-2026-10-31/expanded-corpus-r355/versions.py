exec(compile((__import__('pathlib').Path(__file__).parent/'research.py').read_text(),'research.py','exec'))
for key,terms in [('5c1353d652eb9e10',['bicoloring','Conjecture 4.6']),('8efbe8ae1af9041d',['Theorem 1.8','Claim 1','Claim 2','Claim 3']),('5aeb163217a7084f',['incidence algebra','Conjecture 4.1'])]:
 p=P/'sources'/(key+'.txt'); lines=p.read_text().splitlines(); shown=set(); print('SOURCE',key)
 for n,s in enumerate(lines):
  if any(t in s for t in terms):
   for j in range(max(0,n-2),min(len(lines),n+12)):
    if j not in shown: print(str(j+1)+': '+lines[j]); shown.add(j)
 js('version-read-'+key+'.json',dict(path=str(p.relative_to(P)),lines_read=sorted(j+1 for j in shown)))
