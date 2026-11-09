import itertools,json
for n in range(1,5):
 pairs=[(i,j) for i in range(n) for j in range(n) if i!=j];count=0
 for g in range(1<<len(pairs)):
  a=[0]*n
  for k,(i,j) in enumerate(pairs):
   if g>>k&1:a[i]|=1<<j
  good=[]
  for s in range(1,1<<n):
   out=0;ind=True
   for i in range(n):
    if s>>i&1:
     if a[i]&s:ind=False;break
     out|=a[i]
   if not ind:continue
   closed=s|out;reach=closed
   for i in range(n):
    if out>>i&1:reach|=a[i]
   if reach==(1<<n)-1:good.append((s,closed))
  if not any(2*c.bit_count()>=n for s,c in good):print('FAIL-large',n,g,flush=True);raise SystemExit()
  # exact sqrt comparisons for structural disjunction
  allowed=0
  for s,c in good:allowed|=s
  high=any((a[y].bit_count()+1)**2>=n for y in range(n) if allowed>>y&1)
  if not high:
   acyclic=False
   for s in range(1,1<<n):
    if s.bit_count()**2<n:continue
    remain=s
    while remain:
     v=next((i for i in range(n) if remain>>i&1 and not any(remain>>j&1 and a[j]>>i&1 for j in range(n))),None)
     if v is None:break
     remain^=1<<v
    if not remain:acyclic=True;break
   if not acyclic:print('FAIL-structural',n,g,flush=True);raise SystemExit()
  count+=1
 print(json.dumps({'n':n,'all_labeled_loopless_digraphs_including_digons':count,'large_failures':0,'structural_failures':0}),flush=True)
