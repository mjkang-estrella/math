import itertools as it,json,pathlib,hashlib,re,math
D=pathlib.Path(__file__).resolve().parent;A=D.parent/'expanded-corpus-r49'; C=json.loads((A/'lean/certificates.json').read_text())
# Own polynomial implementation, coefficients ascending, in F5[T]/(f).
f=[2,0,0,0,0,0,2,1,1]
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def rem(a,b=f):
 a=trim([v%5 for v in a]);b=trim(b[:])
 while len(a)>=len(b) and a!=[0]:
  k=len(a)-len(b); c=a[-1]*pow(b[-1],-1,5)%5
  for j,v in enumerate(b):a[j+k]=(a[j+k]-c*v)%5
  trim(a)
 return a
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return rem(c)
def power(a,n):
 r=[1]
 while n:
  if n&1:r=mul(r,a)
  a=mul(a,a);n//=2
 return r
def sub(a,b):return trim([(a[i] if i<len(a) else 0)-(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])
def gcd(a,b):
 while b!=[0]:a,b=b,rem(a,b)
 return a
T=[0,1];x=[0,2,4,1]
assert power(T,5**8)==T
# Rabin for degree8: only prime divisor of8 is2.
assert len(gcd(f,rem(sub(power(T,5**4),T))))==1
for a,y in C['cube_roots']:assert power(y,3)==rem(sub(x,[a]))
for a,h in C['inverses']:assert mul(rem(sub(x,[a])),h)==[1]
assert power(x,5)!=x
admissible=[r for r in range(1,9) if (5**8-1)%(5**r-1)==0 and ((5**8-1)//(5**r-1))%3==0];assert admissible==[1]
ls=[frozenset(map(int,t)) for t in ['023','245','358','278','136','068','014','467','157']]
assert len(set(ls))==9 and all(len(l)==3 for l in ls)
assert all(sum(p in l for l in ls)==3 for p in range(9))
assert all(sum(p in l and q in l for l in ls)<=1 for p,q in it.combinations(range(9),2))
cl=[s for n in range(10) for s in it.combinations(range(9),n) if all(ls[i]&ls[j] for i,j in it.combinations(s,2))];assert max(map(len,cl))==4 and (0,1,2,3) in cl
tris=[]
for i,j,k in it.combinations(range(9),3):
 ij=ls[i]&ls[j];jk=ls[j]&ls[k];ik=ls[i]&ls[k]
 if len(ij)==len(jk)==len(ik)==1 and len(ij|jk|ik)==3:tris.append((i,j,k))
counts=[sum(((b>>i)&1)==((b>>j)&1)==((b>>k)&1) for i,j,k in tris) for b in range(512)]
assert len(tris)==21 and min(counts)==1
out={'355956':{'field_order':5**8,'irreducible_by_Rabin':True,'frobenius':True,'cube_and_inverse_identities':10,'admissible_r':admissible,'x_not_fixed_by_frobenius5':True},'355701':{'triangles':tris,'colorings':512,'minimum_mono_diagnostic':min(counts),'max_pairwise':4,'clique4':[0,1,2,3]},'false_control':{'assert_x_fixed_by_5':power(x,5)==x,'assert_exists_triangle_free_coloring':0 in counts}}
(D/'independent.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
# Manifest, exact result count, input binding supplementary receipt.
manifest=json.loads((A/'MANIFEST.json').read_text())['files'];bad=[s for s,h in manifest.items() if hashlib.sha256((A/s).read_bytes()).hexdigest()!=h];assert not bad
r=json.loads((A/'results.json').read_text());assert len(r)==40
extra=[A/'sources'/s for s in ['x-2101.09652/main.tex','x-2209.00864/main.tex','ALCO_2023__6_4_901_0.tex','x-2208.06912/template.tex','ejgta-1710.pdf','ejgta-1710.txt']]
(D/'source-receipt.json').write_text(json.dumps({'manifest_bindings':len(manifest),'mismatches':bad,'literal_result_entries':len(r),'primary_body_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in extra},'result_entries':{k:r[k] for k in ['355956','355701']}},indent=2))
