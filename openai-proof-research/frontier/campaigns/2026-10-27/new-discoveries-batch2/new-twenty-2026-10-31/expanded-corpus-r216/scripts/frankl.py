import sys
p,q=map(int,sys.argv[1:]);tested=0
for mask in range(1,1<<(p*q)):
 nb=[(mask>>(i*q))&((1<<q)-1) for i in range(p)];sets=set()
 for A in range(1<<p):
  banned=0
  for i in range(p):
   if A>>i&1:banned|=nb[i]
  B=((1<<q)-1)^banned
  # maximal iff every excluded left vertex has a neighbor in B
  if all(A>>i&1 or nb[i]&B for i in range(p)):sets.add(A|(B<<p))
 total=len(sets);freq=[sum(s>>i&1 for s in sets) for i in range(p+q)]
 assert min(freq[:p])*2<=total and min(freq[p:])*2<=total,(mask,total,freq)
 tested+=1
print('PASS bipartition sizes',p,q,'all nonempty labelled edge subsets',tested)
print('Diagnostics only; many cases lie in known classes.')
