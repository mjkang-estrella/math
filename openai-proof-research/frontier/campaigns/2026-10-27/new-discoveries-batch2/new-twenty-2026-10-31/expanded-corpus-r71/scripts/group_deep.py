import itertools as it, math,json,pathlib,sys,time
D=pathlib.Path(__file__).resolve().parents[1];n=int(sys.argv[1]);units=[u for u in range(n) if math.gcd(u,n)==1];reps=set();t=time.monotonic()
for tail in it.combinations(range(1,n),3):
 a=(0,)+tail;reps.add(min(tuple(sorted((u*(x-shift))%n for x in a)) for shift in a for u in units))
tests=0
for j,a in enumerate(sorted(reps)):
 for tail in it.combinations_with_replacement(range(n),3):
  b=(0,)+tail;ok=any(len({(x+y)%n for x,y in zip(a,c)})==4 for c in it.permutations(b));tests+=1
  if not ok:raise RuntimeError((a,b))
 print(json.dumps({'n':n,'completed_A_orbits':j+1,'total_A_orbits':len(reps),'B_multisets_per_A':math.comb(n+2,3),'tests':tests,'counterexamples':0,'seconds':time.monotonic()-t}),flush=True)
(D/f'outputs/group-{n}.json').write_text(json.dumps({'n':n,'k':4,'affine_A_orbits':len(reps),'B_multisets_containing_zero_per_A':math.comb(n+2,3),'tests':tests,'counterexamples':0,'seconds':time.monotonic()-t},indent=2)+'\n')
