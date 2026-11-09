import itertools as it,json,time
start=time.monotonic()
for m in [2,3,4]:
 N=1<<m;count=conn=qcount=fail=0
 for Sbits in range(1,1<<(N-1)):
  S=[s for s in range(1,N) if Sbits>>(s-1)&1];count+=1
  reach={0}
  for s in S:reach|={a^s for a in list(reach)}
  if len(reach)<N:continue
  conn+=1
  lam=[sum(1 if (a&s).bit_count()%2==0 else -1 for s in S) for a in range(N)]
  classes=[{a for a in range(N) if lam[a]==v} for v in sorted(set(lam),reverse=True)]
  good=False
  for C in classes[1:]:
   used={0};layers=[{0}]
   for j in range(1,len(classes)):
    new=used|{a^b for a in used for b in C};delta=new-used
    if not delta or delta not in classes:break
    layers.append(delta);used=new
   else:
    if len(used)==N:good=True;break
  if not good:continue
  qcount+=1
  # E_C(x,y)=N^-1 sum_{a in C} (-1)^{a.(x xor y)}.
  # Entrywise products correspond to convolution of the character classes.
  closed=True
  for C in classes:
   for D in classes:
    conv=[sum((a^b)==x for a in C for b in D) for x in range(N)]
    if any(len({conv[a] for a in B})>1 for B in classes):closed=False
  fail+=not closed
  if not closed:print('FAIL',m,S,classes,flush=True)
 print(json.dumps(dict(m=m,connection_sets=count,connected=conn,Q_polynomial=qcount,hadamard_failures=fail,seconds=time.monotonic()-start)),flush=True)
