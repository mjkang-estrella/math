import json,pathlib,hashlib
W=pathlib.Path(__file__).resolve().parent
c=[1];rows=[];D={}
for n in range(1,122):
 c += [0]*n
 for i in range(len(c)-1,n-1,-1):c[i]-=c[i-n]
 if n%2 and n>=35:
  m=max(map(abs,c));loc=[i for i,x in enumerate(c) if abs(x)==m];rec={'n':n,'maximum_absolute_coefficient':m,'locations':loc,'symmetry_checked':all(c[-1-i]==-c[i] for i in range(len(c)))}
  if len(loc)==2:
   D[n]=loc[1]-loc[0]
   if n>=61:rec['E_tilde']=D[n]-D[n-2]
  rows.append(rec)
out={'scope':'Exact integer coefficient recurrence through n=121; finite evidence only. 344428 is a source wording ambiguity, not credit. 344432 has no full-scope proof here.','reciprocity_proof':'Let N=n(n+1)/2. q^N P_n(1/q)=product(q^j-1)=(-1)^n P_n(q). For odd n, nonzero absolute maxima pair at i,N-i; a central coefficient is zero. Thus literal unique absolute maximum is impossible. Source immediately distinguishes positive maximum and negative minimum and says two terms; no mathematical discovery credit.','rows':rows}
(W/'bounded-check.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'n35':rows[0],'odd_cases':len(rows),'E_tilde_values':sorted({r['E_tilde'] for r in rows if 'E_tilde'in r})}))
