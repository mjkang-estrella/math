import pathlib,json,itertools,math,time
L=pathlib.Path(__file__).resolve().parent
def deck(a,j):return sorted(math.prod(c) for c in itertools.combinations(a,j))
def search():
 counts={};start=time.monotonic()
 for r in [12,24,36,48,60,72,120,180,240,360,720,840,1260,1680,2520]:
  ds=[d for d in range(1,r+1) if r%d==0];triples={};ct=0
  for t in itertools.combinations_with_replacement(ds,3):
   p=math.prod(t);delta=sum(x-r//x for x in t)
   triples.setdefault((p,delta),[]).append(t)
  for (p,delta),ts in triples.items():
   if r**3%p:continue
   for t in ts:
    for u in triples.get((r**3//p,-delta),[]):
     a=sorted(t+u);b=sorted(r//x for x in a);ct+=1
     if a!=b:
      assert sum(a)==sum(b) and deck(a,3)==deck(b,3)
      return dict(r=r,a=a,b=b,total=sum(a),deck=deck(a,3),counts=counts,seconds=time.monotonic()-start)
  counts[r]=dict(divisors=len(ds),triple_keys=len(triples),candidate_pairs=ct)
 return dict(found=False,counts=counts,seconds=time.monotonic()-start)
if __name__=='__main__':
 result=search();(L/'check-results.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
