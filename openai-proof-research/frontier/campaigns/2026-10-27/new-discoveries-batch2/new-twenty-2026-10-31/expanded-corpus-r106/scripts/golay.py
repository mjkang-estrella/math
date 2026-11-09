import itertools,json
out=[]
for n in [2,4,8,10,16,20]:
 # exact autocorrelation buckets for every +/-1 sequence, inversion symmetry A[0]=1
 by={};pairs=0;bad=0;compressions=set()
 for tail in itertools.product([-1,1],repeat=n-1):
  a=(1,)+tail;key=tuple(sum(a[i]*a[(i+s)%n] for i in range(n)) for s in range(1,n//2+1))
  comp=(sum(a[::2]),sum(a[1::2]));by.setdefault(key,set()).add(comp)
 for key,aa in by.items():
  for a in aa:
   for b in by.get(tuple(-v for v in key),[]):
    pairs+=1;compressions.add((a,b));x,y=sum(a),sum(b)
    # invariants of forms after signs, swapping sequences, shifts, alt neg
    alt=(a[0]-a[1],b[0]-b[1]);target=sorted([abs(x),abs(y)])
    if sorted(map(abs,alt))!=target:bad+=1
 out.append({'v':n,'autocorrelation_buckets':len(by),'compression_pairs_tested':pairs,'bad_magnitude_pairs':bad});print(out[-1],flush=True)
 open('outputs/golay-small.json','w').write(json.dumps(out,indent=2))
