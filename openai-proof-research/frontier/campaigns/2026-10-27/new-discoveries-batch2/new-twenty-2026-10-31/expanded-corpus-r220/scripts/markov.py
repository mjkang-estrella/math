import itertools,json,pathlib,random,time
L=pathlib.Path(__file__).resolve().parents[1];start=time.monotonic();counts={};rng=random.Random(220)
def test(n,edges):
 full=(1<<n)-1;pred=[0]*n
 for u,v in edges:pred[v]|=1<<u
 def anc(S,avoid):
  old=-1
  while old!=S:
   old=S
   for v in range(n):
    if S>>v&1:S|=pred[v]&~avoid
  return S
 if any(anc(1<<i,0)!=full for i in range(n)):return 'not_strong'
 def free(I,J):return anc(I,J)&anc(J,I)==0
 adj=[0]*n
 for i in range(n):
  for j in range(i):
   if free(1<<i,1<<j):adj[i]|=1<<j;adj[j]|=1<<i
 comps=[];unseen=full
 while unseen:
  C=unseen&-unseen;old=-1
  while C!=old:
   old=C
   for i in range(n):
    if C>>i&1:C|=adj[i]
  comps.append(C);unseen&=~C
 for A,B in itertools.combinations(comps,2):
  I=A
  while I:
   J=B
   while J:
    if (I!=A or J!=B) and free(I,J):
     if not any((A^I)>>i&1 and free(I|1<<i,J) or (B^J)>>i&1 and free(I,J|1<<i) for i in range(n)):
      return {'n':n,'edges':edges,'K1':A,'K2':B,'I':I,'J':J}
    J=(J-1)&B
   I=(I-1)&A
 return 'pass'
for n in range(2,5):
 pairs=list(itertools.permutations(range(n),2));ct={}
 for bits in range(1<<len(pairs)):
  result=test(n,[e for k,e in enumerate(pairs) if bits>>k&1]);key=result if isinstance(result,str) else 'COUNTEREXAMPLE';ct[key]=ct.get(key,0)+1
  if isinstance(result,dict):print(result,flush=True);(L/'outputs/markov-candidate.json').write_text(json.dumps(result))
 counts[str(n)]=ct;print(n,ct,flush=True)
for n in range(5,11):
 ct={}
 for z in range(3000):
  p=rng.choice([.12,.2,.3,.5,.7]);edges=[(i,j) for i in range(n) for j in range(n) if i!=j and rng.random()<p];result=test(n,edges);key=result if isinstance(result,str) else 'COUNTEREXAMPLE';ct[key]=ct.get(key,0)+1
  if isinstance(result,dict):print(result,flush=True);(L/'outputs/markov-candidate.json').write_text(json.dumps(result));break
 counts[str(n)]=ct;(L/'outputs/markov-data.json').write_text(json.dumps(counts,indent=2));print(n,ct,flush=True)
