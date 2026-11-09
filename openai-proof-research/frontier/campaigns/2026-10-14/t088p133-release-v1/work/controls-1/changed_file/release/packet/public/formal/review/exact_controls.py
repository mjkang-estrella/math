"""Independent exact rational checks of retained hypotheses; MIT, 2026 Myeongjin Kang."""
from fractions import Fraction as F
import json

def check():
 # alpha,beta,p,q,d,P,N,value,omitted hypothesis
 rows=[
 ('nonvacuity',['2/3','4/3','1/3','2/3','3/2','1/2','4/3'],'12/13',None),
 ('zero_d',['1','1','1/2','1/2','0','1','1'],'1/3',None),
 ('nonstrict_equality',['1','1','1/2','1/2','1','1/2','1/2'],'1','strict_first'),
 ('missing_first',['1','1','1/2','1/2','1','1/8','1/2'],'13/10','first'),
 ('missing_second',['1','1','1/2','1/2','1','1','1/8'],'17/15','second'),
 ('missing_sum',['2','2','1/2','1/2','1','1','1/2'],'7/6','sum'),
 ('missing_alpha',['-2','4','1/2','1/2','1','3/4','1/2'],'24/5','alpha'),
 ('missing_beta',['4','-2','1/2','1/2','1','1','3/4'],'14/3','beta'),
 ('missing_weight',['1','1','1/2','1','0','1/8','1/4'],'6/5','weight'),
 ('missing_range',['1','1','2','-1','0','1','2'],'7/3','p_upper')]
 results=[]
 for name,data,value,omitted in rows:
  a,b,p,q,d,P,N=map(F,data)
  checks={'alpha':a>0,'beta':b>0,'sum':a+b==2,'p_lower':p>0,'p_upper':p<1,
   'weight':q==1-p,'d_nonneg':d>=0,'P_pos':P>0,'N_pos':N>0,
   'first':2*d*p*p<P,'second':2*d*q*q<=N}
  assert p and q and a+P/p and b+N/q
  actual=(1+d)*(p*a/(a+P/p)+q*b/(b+N/q))
  assert actual==F(value)
  if omitted=='strict_first':
   assert not checks['first'] and 2*d*p*p==P and actual==1
   omitted='first'
  elif omitted=='first':assert not (2*d*p*p<=P) and actual>1
  elif omitted: assert not checks[omitted] and actual>1
  else: assert actual<1
  assert all(v for k,v in checks.items() if k!=omitted)
  results.append({'case':name,'parameters':data,'value':str(actual),'hypotheses':checks,
   'nonzero_divisors':[str(p),str(q),str(a+P/p),str(b+N/q)],'expected':True})
 assert F(2)*F('3/2')*F('2/3')**2==F('4/3')
 return results
if __name__=='__main__':print(json.dumps(check(),indent=2))
