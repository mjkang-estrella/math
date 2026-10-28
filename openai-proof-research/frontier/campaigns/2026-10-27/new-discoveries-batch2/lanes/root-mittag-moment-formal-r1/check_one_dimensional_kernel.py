from pathlib import Path
import json
import mpmath as mp
mp.mp.dps=65
rows=[]
for v,w in [(mp.mpf(1),mp.mpf(1)),(mp.mpf(1)/7,mp.mpf(13)),(mp.mpf(20),mp.mpf(1)/100),(mp.mpf(3)/5,mp.mpf(7)/11)]:
 for t in [mp.mpf(0),mp.mpf(1)/100,mp.mpf(1)/3,mp.mpf(1),mp.mpf(2)]:
  e=lambda x:mp.exp(-x)*(1+1j*mp.erfi(mp.sqrt(x)))
  K=mp.re(e(v*t)*mp.conj(e(w*t)))
  J=2*mp.sqrt(v*w)/mp.pi*(mp.quad(lambda u:mp.exp(-t*w*(1-u*u))/(v+w*u*u),[0,1])+mp.quad(lambda u:mp.exp(-t*v*(1-u*u))/(w+v*u*u),[0,1]))
  err=abs(K-J)
  assert err<mp.mpf('1e-57'),(v,w,t,err)
  rows.append({'v':str(v),'w':str(w),'t':str(t),'absolute_error':str(err)})
record={'scope':'Diagnostic numerical check only, not a proof or Lean certification','precision_decimal_digits':65,'cases':len(rows),'status':'PASS','rows':rows}
Path('one-dimensional-kernel-checks.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS',len(rows),'diagnostic identities')
