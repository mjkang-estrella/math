import pathlib,itertools,collections,json,time,random
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(246);rows=[];start=time.monotonic()
for dims in [(2,2),(2,2,2),(3,3),(2,4),(4,4),(2,2,3),(2,2,2,2),(3,6),(5,5),(24,)]:
 G=list(itertools.product(*(range(d) for d in dims)));q=len(G);ix={g:i for i,g in enumerate(G)};add=[[ix[tuple((x+y)%d for x,y,d in zip(a,b,dims))] for b in G] for a in G]
 for n in range(3,min(8,q)):
  count=unit=pre=0
  for t in range(3000):
   A=tuple(sorted(rng.sample(range(q),n)));B=tuple(sorted(rng.sample(range(1,q),n)));count+=1;hist=collections.Counter();ok=True
   for perm in itertools.permutations(B):
    sums=tuple(add[a][b] for a,b in zip(A,perm))
    if any(s in A for s in sums):continue
    if len(set(sums))<n:ok=False;break
    hist[tuple(sorted(sums))]+=1
   if ok and hist:
    unit+=1
    if 1 in hist.values():
     pre+=1
     if max(hist.values())>1:print('COUNTEREXAMPLE',dims,A,B,hist,flush=True);raise SystemExit
   if time.monotonic()-start>85:break
  row=dict(group=dims,size=n,sampled_pairs=count,unit=unit,premise=pre);rows.append(row);print(row,flush=True)
  if time.monotonic()-start>85:break
 if time.monotonic()-start>85:break
(D/'matching-deep-coverage.json').write_text(json.dumps(rows,indent=2))
