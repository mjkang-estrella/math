from fractions import Fraction as F
import pathlib,json
L=pathlib.Path(__file__).resolve().parent
count=0
# Independent overlap computation by sorting the four interval endpoints,
# then testing each open cell. No use of the candidate's overlap helper.
for a in [F(1,7),F(2,3),F(1),F(7,2),F(11)]:
 for k in range(-8,41):
  s=a*F(k,12)
  ends=sorted(set([F(0),a,s-a,s]))
  length=sum((v-u for u,v in zip(ends,ends[1:]) if 0<(u+v)/2<a and s-a<(u+v)/2<s),F(0))
  target=max(F(0),min(s,2*a-s))
  assert length==target
  count+=1
# New tail certificate: exp(t)>=t^4/24 gives, for a>=10,
# exp(-a/4)(2a+10)<=6144(2a+10)/a^4<=18432/a^3.
# With a_n>=a_2=18432 and first term 1/[24(n-1)], the bound
# is <=1/24+1/18432^2<1/6. Universal proof uses only monotonicity.
worst=F(1,24)+F(1,18432**2)
assert worst<F(1,6)
assert F(6144*3,1)==18432
assert 1+1+F(1,2)+F(1,4)<3 # factorial geometric bound for exp(1)
rows=[]
for n in range(2,101):
 p=1-F(1,n);a=2*(48*n)**n
 first=F(1,24*(n-1));tail=F(18432,a**3)
 assert a>=18432 and first+tail<=worst
 # (a/2)^(1/n)=48*n checked as integer identity, no real pow approximation.
 assert (48*n)**n==a//2
 rows.append({'n':n,'first':str(first),'new_tail_certificate_pass':first+tail<F(1,6)})
with (L/'checker-results.jsonl').open('w') as f:
 f.write(json.dumps({'overlap_exact_cases':count,'all_n_worst_bound':str(worst),'J_lower_bound':'1/6','universal_certificate_pass':True})+'\n')
 for r in rows:f.write(json.dumps(r)+'\n')
print(json.dumps({'overlap_exact_cases':count,'cofinal_exact_cases':len(rows),'universal_bound':str(worst),'pass':True}))
