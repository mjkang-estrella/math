import pathlib,itertools,collections,json,time
D=pathlib.Path(__file__).resolve().parents[1]; out=[]; started=time.monotonic()
for q in range(3,15):
 for n in range(2,min(5,q)):
  pairs=eligible=acyclicpairs=0
  for A in itertools.combinations(range(q),n):
   for B in itertools.combinations(range(1,q),n):
    pairs+=1;hist=collections.Counter();allunit=True
    for perm in itertools.permutations(B):
     sums=tuple((a+b)%q for a,b in zip(A,perm))
     if any(s in A for s in sums):continue
     if len(set(sums))!=n:allunit=False;break
     hist[tuple(sorted(sums))]+=1
    if not allunit or not hist:continue
    eligible+=1
    if 1 in hist.values():
     acyclicpairs+=1
     if max(hist.values())>1:
      print('COUNTEREXAMPLE',q,A,B,hist,flush=True);raise SystemExit
    if time.monotonic()-started>90:break
   if time.monotonic()-started>90:break
  row=dict(q=q,n=n,pairs=pairs,unit_matching_pairs=eligible,premise_pairs=acyclicpairs,complete=time.monotonic()-started<=90);out.append(row);print(row,flush=True)
  if time.monotonic()-started>90:break
 if time.monotonic()-started>90:break
(D/'matching-coverage.json').write_text(json.dumps(out,indent=2))
