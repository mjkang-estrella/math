"""Deterministic checks of i13 obstruction examples. No finite check is a proof."""
import collections, fractions, itertools, json, math, pathlib
ROOT=pathlib.Path(__file__).resolve().parents[3]
OUT=ROOT/'frontier/experiments/i13_fresh_discovery'
F=fractions.Fraction

def score_barrier():
 counts={}; examples=[]
 for a in range(2,5):
  for b in range(2,5):
   count=0
   for mask in range(1,1<<(a*b)):
    edges=[(i,j) for i in range(a) for j in range(b) if mask>>(i*b+j)&1]
    dl=[sum(i==u for i,j in edges) for u in range(a)]
    dr=[sum(j==v for i,j in edges) for v in range(b)]
    if min(dl+dr)==0 or len(set(dl))>1 or len(set(dr))>1:continue
    count+=1
    for seed in range(3):
     s=[(i*i+7*seed*i+5)%17-8 for i in range(a)]
     t=[(3*j*j+5*seed*j+2)%19-9 for j in range(b)]
     w=[[(11*i+7*j+seed*i*j+3)%23-11 for j in range(b)] for i in range(a)]
     identity=sum(s)+sum(t)+sum(w[i][j] for i,j in edges)
     collapsed=[a*s[i]+b*t[j]+len(edges)*w[i][j] for i,j in edges]
     assert sum(collapsed)==len(edges)*identity
     assert max(collapsed)>=identity
   counts[f'{a}x{b}']=count
 # A genuine 6/3-biregular triangulated torus, rather than a cycle toy.
 m=4; ix=lambda x,y:(x%m)*m+y%m
 faces=[]
 for x in range(m):
  for y in range(m):
   faces += [tuple(sorted((ix(x,y),ix(x+1,y),ix(x+1,y+1)))),tuple(sorted((ix(x,y),ix(x,y+1),ix(x+1,y+1))))]
 assert len(set(faces))==32
 degrees=collections.Counter(v for f in faces for v in f)
 pairs=collections.Counter(tuple(sorted(e)) for f in faces for e in itertools.combinations(f,2))
 assert set(degrees.values())=={6} and set(pairs.values())=={2}
 return {'biregular_graphs_checked':counts,'total_graphs':sum(counts.values()),'scores_per_graph':3,'torus':{'vertices':16,'faces':32,'incidences':96,'point_degree':6,'face_degree':3,'each_point_pair_in_faces':2},'meaning':'Exact score identity and explicit biregular test complex; does not assert Sidorenko violation.'}

def projection():
 counts=collections.Counter()
 for p in itertools.permutations(range(4)):
  counts[(int(p[0]==0),int(p[1]==1))]+=1
 assert counts=={(0,0):14,(0,1):4,(1,0):4,(1,1):2}
 A={frozenset('ab'),frozenset('ac')};B={frozenset('ab'),frozenset('bc')}
 proj=lambda fam:{s&frozenset('c') for s in fam}
 assert proj(A&B)=={frozenset()} and proj(A)&proj(B)=={frozenset(),frozenset('c')}
 q=20
 return {'K44_fibers':{''.join(map(str,k)):v for k,v in sorted(counts.items())},'odds_ratio':str(F(counts[0,0]*counts[1,1],counts[0,1]*counts[1,0])),'component_power':q,'distinct_projections':4**q,'full_bases':24**q,'fiber_max_min_ratio':7**q,'inverse_fiber_estimator_relative_second_moment':str(F(45,28)**q),'optimal_inverse_fiber_rejection_acceptance':str(F(1,3)**q),'incompatible_extension':{'M1':['ab','ac'],'M2':['ab','bc'],'retain':'c','actual_projection':['empty'],'intersection_of_projections':['empty','c']}}

def gaussian():
 c=(2/math.pi)**2; const=c*(8/3)*2**(-1/4);rows=[]
 for n in [64,256,1024,4096,16384,65536,262144]:
  main=n*c; total=float(n)
  for h in range(1,n):
   r=(1+h)**(-.25); s=(1+2*h)**(-.25)
   main+=2*c*(n-h)*r*s
   total+=2*c*(n-h)*math.asin(r)*math.asin(s)
  rem=total-main
  assert rem>0
  rows.append({'N':n,'main_variance_over_N_to_1_5':main/n**1.5,'limit_constant':const,'remainder_over_main':rem/main,'total_variance_over_N':total/n,'remainder_over_NlogN':rem/(n*math.log(n))})
 # Independent pure-Python matrix calculation of the fourth moment.
 moments=[]
 for n in [4,8,16,32]:
  a=[[(1+abs(i-j))**(-.25) for j in range(n)] for i in range(n)]
  b=[[(1+2*abs(i-j))**(-.25) for j in range(n)] for i in range(n)]
  ab=[[sum(a[i][k]*b[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
  v=sum(ab[i][i] for i in range(n)); tr2=sum(ab[i][j]*ab[j][i] for i in range(n) for j in range(n))
  fourth_ratio=3*(1+2*tr2/v**2)
  assert 3<=fourth_ratio<=9+1e-12
  direct=n+2*sum((n-h)*(1+h)**(-.25)*(1+2*h)**(-.25) for h in range(1,n))
  assert abs(v-direct)<1e-9
  moments.append({'N':n,'fourth_moment_over_variance_squared':fourth_ratio})
 return {'type':'floating-point deterministic covariance sums, not simulation or proof','rows':rows,'matrix_fourth_moment_check':moments}

# The local activation matrix is evaluated from the two branch probabilities,
# independently of its simplified diagonal/off-diagonal description.
def activation():
 theta=F(1,2); gamma=126; maxset=127; counts=collections.Counter()
 for a in range(1,128):
  for b in range(1,128):
   q=a|b;r=a^b
   value=F(1,2)*(int(r==0)+theta*int(r==gamma))
   if q & ~gamma == 0:value+=F(1,2)*(int(r==0)-theta*int(r==gamma))
   expected=(F(1) if a&1==0 else F(1,2)) if a==b else (F(1,4) if r==gamma and q&1 else F(0))
   assert value==expected;counts[str(value)]+=1
 assert counts['1']==63 and counts['1/2']==64 and counts['1/4']==64
 return {'local_matrix_entry_counts':dict(counts),'constant_map_diagonal_terms':63,'torus_incidence_count':96,'automorphism_upper_bound':192,'normalized_signed_average_lower_bound':str(F(63*96)-192*F(1,4)**96)}

result={'activation':activation(),'score_barrier':score_barrier(),'projected_counting':projection(),'long_memory':gaussian()}
(OUT/'diagnostics.results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
