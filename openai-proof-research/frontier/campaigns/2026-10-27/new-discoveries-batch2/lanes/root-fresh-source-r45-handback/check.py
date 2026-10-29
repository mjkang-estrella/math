import sympy as s, json, math
from pathlib import Path
x,t=s.symbols('x t');out={}
# Real cyclotomic minimal polynomials, independently recovered via resultant.
def realpoly(n):
 z=s.symbols('z');r=s.resultant(s.cyclotomic_poly(n,z), z*z-t*z+1,z)
 coeff,factors=s.factor_list(r,t)
 assert coeff==1 and len(factors)==1 and factors[0][1]==2
 return s.Poly(factors[0][0],t).monic().as_expr()
rows=[]
for n in [5,7,8,9,10,12,15,21,30]:
 f=realpoly(n); rows.append({'n':n,'realpoly':str(f),'norm_d':int((-1)**s.degree(f,t)*f.subs(t,-6))})
out['real_cyclotomic_norms']=rows
f=realpoly(15)
assert f==t**4-t**3-4*t**2+4*t+1
assert f.subs(t,-6)==1345==5*269
assert s.Poly(f-(t+1)**4,t,modulus=5).is_zero
sqrt5=1+2*t**3-6*t
assert s.rem(sqrt5**2-5,f,t)==0
out['actual_squareclass_obstruction_n15']={'sqrt5_in_K15':str(sqrt5),'d5':5,'consequence':'d5 already square in base field; independent-radicals criterion cannot handle this conductor'}
out['overlap_n15']={'f':str(f),'mod5':'(t+1)^4','norm_d1':1345,'d5':5,'residue_map':'t -> -1 mod5; d1=t+6 ->0; d5=5 ->0'}
# n8: d2=6 in Q(sqrt2) has square norm 36 but is nonsquare.
# (a+b sqrt2)^2=6 implies ab=0; a^2=6 or b^2=3, impossible rational squares.
assert s.integer_nthroot(6,2)[1] is False and s.integer_nthroot(3,2)[1] is False
out['norm_square_shortcut']={'n':8,'j':2,'d':6,'norm':36,'rational_square_alternatives':[6,3]}
# Exact classical conductor7 product via real minimal polynomial.
f7=realpoly(7);assert f7.subs(t,-6)==-169
out['n7_squareclass_dependency']={'product_d1_d2_d3':169,'square_root':13}
# Pell primitive parts by integer divisor recurrence; compare exact real norms
# for odd n, product primitive d_j = L_n.
pell=[0,1];L={1:1}
for n in range(2,61):pell.append(2*pell[-1]+pell[-2])
for n in range(2,61):
 den=math.prod(L[d] for d in range(1,n) if n%d==0)
 assert pell[n]%den==0;L[n]=pell[n]//den
for row in rows:
 if row['n']%2: assert row['norm_d']==L[row['n']]
assert L[7]==169 and L[30]==961
out['primitive_pell_parts_through60']={str(n):L[n] for n in range(1,61)}
out['square_values_n2_through60']=[n for n in range(2,61) if math.isqrt(L[n])**2==L[n]]
assert out['square_values_n2_through60']==[7,30]
# Fel: uniform-sum moment EGF, centered parity gives source binomial recurrence.
felchecks=0
for weights in [(1,), (1,2), (1,2,3), (2,3,5,7)]:
 N=13;F=s.Integer(1)
 for w in weights:
  F=s.series(F*sum(s.Rational(w**k,math.factorial(k+1))*x**k for k in range(N)),x,0,N).removeO().expand()
 T=[s.expand(F).coeff(x,k)*math.factorial(k) for k in range(N)]
 for degree in range(1,N,2):
  assert s.expand(sum((-1)**k*s.binomial(degree,k)*T[1]**k*T[degree-k] for k in range(degree+1)))==0
  felchecks+=1
out['fel_already_public_recurrence_checks']=felchecks
out['status']='PASS finite exact identities and route obstructions only; no source resolution'
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
