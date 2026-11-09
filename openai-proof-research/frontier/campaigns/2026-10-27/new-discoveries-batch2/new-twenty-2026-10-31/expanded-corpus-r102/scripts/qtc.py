import itertools,json
for a in [2,3]:
 for c in range(4):
  count=0
  for vals in itertools.product(range(c+1),repeat=a*a):
   if any(vals[i*a+j]<vals[i*a+j+1] for i in range(a) for j in range(a-1)):continue
   if any(vals[i*a+j]<vals[(i+1)*a+j] for i in range(a-1) for j in range(a)):continue
   if any(vals[i*a+j]+vals[(a-1-j)*a+a-1-i]!=c for i in range(a) for j in range(a) if i!=j):continue
   count+=1
  print(json.dumps({'a':a,'c':c,'literal_count':count}),flush=True)
