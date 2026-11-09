import pathlib,json,math
D=pathlib.Path(__file__).resolve().parents[1];n=13;c=[0]*((1<<n)*(n+2));total=0
for f in range(1,13):
 o=json.loads((D/f'outputs/pinnacle13-first{f}.json').read_text());total+=o['total'];c=[a+b for a,b in zip(c,o['counts'])]
assert total==math.factorial(n)
bad=[];sets=0
for s in range(1<<n):
 v=c[s*(n+2):(s+1)*(n+2)]
 if not any(v):continue
 sets+=1
 for j in range((n+1)//2+1):
  g=v[j]
  if g<0:bad.append([s,j,g])
  for k in range(n+2-2*j):v[j+k]-=g*math.comb(n+1-2*j,k)
 assert not any(v)
r={'n':n,'total':total,'sets':sets,'bad':bad,'method':'12 disjoint first-value shards, reversal symmetry first < last with reflected inverse descent coefficients'}
(D/'outputs/pinnacle13.json').write_text(json.dumps({'summary':r,'counts':c}));print(r)
