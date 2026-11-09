import itertools,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
cols=[9,6,4,11,6,14,5,1,12];n=9;r=4

def indep(ix):
 for mask in range(1,1<<len(ix)):
  v=0
  for j,i in enumerate(ix):
   if mask>>j&1:v^=cols[i]
  if v==0:return False
 return True
bases=[frozenset(c) for c in itertools.combinations(range(n),r) if indep(c)];bs=set(bases)
assert all(any((A-{e})|{f} in bs for f in B-A) for A in bases for B in bases for e in A-B)
E=frozenset(range(n));parts={x:[B for B in bases if x not in B and E-{x}-B in bs] for x in [1,6]}
common=set(parts[1])&set(parts[6]);print('bases',len(bases),'part1',len(parts[1]),'part6',len(parts[6]),'common',len(common));assert not common
out={'cols':cols,'rank':r,'k':2,'x':1,'y':6,'bases':[sorted(B) for B in bases],'deletion_complementary_bases':{x:[sorted(B) for B in parts[x]] for x in parts},'basis_exchange_checked':True,'common':list(common)}
(D/'matroid-certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'x_partition':[sorted(parts[1][0]),sorted(E-{1}-parts[1][0])],'y_partition':[sorted(parts[6][0]),sorted(E-{6}-parts[6][0])]}))
