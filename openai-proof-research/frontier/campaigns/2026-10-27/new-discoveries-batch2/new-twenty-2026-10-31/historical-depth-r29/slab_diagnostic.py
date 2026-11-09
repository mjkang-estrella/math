import resource,decimal,math,json,pathlib
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(10,10))
D=decimal.Decimal;decimal.getcontext().prec=70
# Unit cube [-1/2,1/2]^n; total slab width t.
# k supported equal coordinates 1/sqrt(k); Irwin-Hall CDF by inclusion-exclusion.
def volume(k,t):
 s=(D(k)+t*D(k).sqrt())/2
 c=sum((-1)**j*D(math.comb(k,j))*max(s-D(j),D(0))**k for j in range(k+1))/D(math.factorial(k))
 return 2*c-1
rows=[]
for it in range(83,201):
 t=D(it)/100;v={k:volume(k,t) for k in [2,3,4,5]}
 if v[4]<min(v[2],v[3],v[5]):rows.append({'t':str(t),'volumes':{str(k):str(x) for k,x in v.items()}})
print(json.dumps({'status':'decimal_diagnostic_only_not_proof_or_source_scope','n':5,'four_support_beats_all_named_directions':rows},indent=2))
