import json,math
from pathlib import Path
O=Path(__file__).parent
out={'suffix':[]}
for n in range(3,6):
 mod=10**n;roots=[x for x in range(mod) if set(str(x*x%mod).zfill(n))<=set('789')];sq=set(x*x%mod for x in roots)
 out['suffix'].append({'n':n,'root_count':len(roots),'distinct_square_suffixes':len(sq),'claimed':8*3**(n-3)})
out['falling_factorial_mismatch']={'n':3,'x':0,'displayed_P':5,'literal_RHS':1+1*(1+1+0),'meaning':'transcription/convention objection only'}
c=0;fail=[];margin=(float('inf'),None)
for n in range(1,10001):
 c+=math.prod(map(int,str(n)))
 if n in [10**k-1 for k in range(1,6)]:continue
 h=25/44*(n**math.log10(45)-1)+5/11*(45*((n+2)/10)**math.log10(45)-1)
 if c>h:fail.append({'n':n,'c':c,'h_approx':h})
 if h-c<margin[0]:margin=(h-c,n)
out['digit_bound']={'positive_n_through':10000,'arithmetic':'floating h; exact c; exploratory only','failures':fail[:10],'failure_count':len(fail),'minimum_margin_approx':margin}
out['catalan_mersenne']=[{'k':k,'n':2**k-1,'residue10':(math.comb(2*(2**k-1),2**k-1)//2**k)%10} for k in range(1,13)]
out['spectral_endpoint']={'ell':2,'lambda1':0,'positive_lower_bound_certificate':'128<225 implies 8sqrt(2)<15','credit':0}
(O/'calculations.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
