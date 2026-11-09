import json,pathlib,itertools
from fractions import Fraction
D=pathlib.Path(__file__).resolve().parents[1]
data=json.loads((D/'sources/matcorr-database.body').read_text())['matroids'];out=[]
for x in data:
 if x['alpha']['numerator']*7<=8*x['alpha']['denominator']:continue
 if x.get('bases') is None:continue
 B=[set(a) for a in x['bases']];i,j=x['max_pairs'][0]['i'],x['max_pairs'][0]['j']
 a=sum(i in b and j in b for b in B);b=sum(i in u and j not in u for u in B);c=sum(j in u and i not in u for u in B);d=sum(i not in u and j not in u for u in B)
 t=Fraction(1,10000);f=a*t*t+(b+c)*t+d;fi=a*t+b;fj=a*t+c
 out.append({'public_id':x['id'],'name':x['name'],'n':x['n'],'rank':x['rank'],'counts':[a,b,c,d],'date_fields':{k:v for k,v in x.items() if 'date' in k.lower() or 'discover' in k.lower() or 'at'==k[-2:]},'rayleigh_ratio_at_t':str(a*f/(fi*fj)),'violates_8_over_7_at_positive_t':7*a*f>8*fi*fj})
print(json.dumps(out,indent=2));(D/'public-matroid-check.json').write_text(json.dumps(out,indent=2)+'\n')
# Independent direct enumeration checks the NextClosure totals through n=4.
for n in range(1,5):
 N=1<<n;closed=norm_hyp=bad=0
 for mask in range(1<<N):
  sets=[a for a in range(N) if mask>>a&1]
  if any(not mask>>(a&b)&1 for a in sets for b in sets):continue
  closed+=1
  if len(sets)<2 or not mask&1 or not mask>>(N-1)&1:continue
  sig=[sum(1<<a for a in sets if a>>j&1) for j in range(n)]
  if len(set(sig))<n:continue
  low=[j for j,s in enumerate(sig) if s.bit_count()*2<=len(sets)]
  if len(low)!=1:continue
  norm_hyp+=1;expected=(1<<(N-1))|sum(1<<a for a in range(N) if not a>>low[0]&1)
  bad+=mask!=expected
 print({'n':n,'direct_closed':closed,'normalized_unique_low':norm_hyp,'normalized_failures':bad},flush=True)
