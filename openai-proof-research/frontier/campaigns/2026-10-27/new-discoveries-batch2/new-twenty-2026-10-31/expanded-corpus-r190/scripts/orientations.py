import pathlib,itertools,json
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for n,delnum in [(6,0),(7,0),(7,1),(7,2),(7,3)]:
 deleted={(2*j,2*j+1) for j in range(delnum)};es=[e for e in itertools.combinations(range(n),2) if e not in deleted];deg=[sum(v in e for e in es) for v in range(n)];seen=set();target=3**(n-1);tested=0
 # Gray-code orientations update the two affected vertex residues.
 beta=[(sum(a==v for a,b in es)-sum(b==v for a,b in es))%3 for v in range(n)];prev=0
 for k in range(1<<len(es)):
  g=k^(k>>1)
  if k:
   j=(g^prev).bit_length()-1;a,b=es[j];sgn=1 if g>>j&1 else -1;beta[a]=(beta[a]+sgn)%3;beta[b]=(beta[b]-sgn)%3
  prev=g;seen.add(tuple(beta));tested+=1
  if len(seen)==target:break
 out.append({'n':n,'deleted_matching_size':delnum,'edges':es,'orientation_prefix_examined':tested,'zero_sum_boundary_functions_reached':len(seen),'required':target})
(D/'outputs/orientations.json').write_text(json.dumps(out,indent=2));print(out)
