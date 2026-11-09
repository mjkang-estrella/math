import itertools,json
# Independent direct column-minor coefficient computation after row insertion.
for n in range(1,10):
 total=0;nonzero=0
 for p in itertools.permutations(range(n)):
  P=[];Q=[]
  for i,a in enumerate(p):
   row=0
   while row<len(P):
    j=next((j for j,v in enumerate(P[row]) if v>a),len(P[row]))
    if j==len(P[row]):P[row].append(a);Q[row].append(i);break
    P[row][j],a=a,P[row][j];row+=1
   else:P.append([a]);Q.append([i])
  sign=1
  for c in range(len(P[0])):
   pc=[row[c] for row in P if len(row)>c];qc=[row[c] for row in Q if len(row)>c]
   images=[p[i] for i in qc]
   if set(images)!=set(pc):sign=0;break
   positions=[pc.index(a) for a in images]
   inv=sum(positions[i]>positions[j] for i in range(len(pc)) for j in range(i+1,len(pc)))
   if inv%2:sign=-sign
  total+=sign;nonzero+=sign!=0
 print(json.dumps({'n':n,'trace':total,'nonzero_diagonal_entries':nonzero}),flush=True)
