import pathlib,json,time
D=pathlib.Path(__file__).resolve().parents[1];start=time.monotonic();out=[]
for n in range(1,6):
 N=1<<n;bits=[1<<a for a in range(N)];fam=0;count=eligible=hyp=fail=0;last=0;complete=False
 def close(f):
  # Repeated intersection completion, no mandatory universe or empty set.
  sets=[a for a in range(N) if f>>a&1]
  i=0
  while i<len(sets):
   a=sets[i]
   for b in sets[:i]:
    c=a&b
    if not f>>c&1:f|=bits[c];sets.append(c)
   i+=1
  return f
 while True:
  count+=1;size=fam.bit_count();sig=[0]*n;un=0;last=fam
  for a in range(N):
   if fam>>a&1:
    un|=a
    for j in range(n):
     if a>>j&1:sig[j]|=bits[a]
  if size>1 and un==N-1 and len(set(sig))==n:
   eligible+=1;low=[j for j,x in enumerate(sig) if 2*x.bit_count()<=size]
   if len(low)==1:
    hyp+=1;expected=bits[N-1]|sum(bits[a] for a in range(N) if not a>>low[0]&1)
    if fam!=expected:
     fail+=1;print('FAILURE',n,fam,low,flush=True)
  found=False
  for i in range(N-1,-1,-1):
   if not fam>>i&1:
    lower=bits[i]-1;g=close((fam&lower)|bits[i])
    if g&lower==fam&lower:fam=g;found=True;break
  if not found:complete=True;break
  if time.monotonic()-start>105:break
 row={'n':n,'closed_families':count,'full_ground_separating':eligible,'unique_low':hyp,'failures':fail,'complete':complete,'last_family_mask':last};out.append(row);print(row,flush=True)
 if not complete:break
(D/'poonen-search.json').write_text(json.dumps(out,indent=2)+'\n')
