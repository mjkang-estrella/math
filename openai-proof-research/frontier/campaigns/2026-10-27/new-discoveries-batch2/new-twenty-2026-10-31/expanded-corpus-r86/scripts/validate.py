from pathlib import Path
import json,hashlib,subprocess
L=Path(__file__).resolve().parents[1];H=lambda b:hashlib.sha256(b).hexdigest();report={}
res=json.loads((L/'results.json').read_text());ids=json.loads((L/'reservation.json').read_text())['ids'];assert set(map(int,res))==set(ids) and len(res)==20
for i in ids:
 r=res[str(i)];raw=(L/f'sources/{i}.jsonl').read_bytes();assert raw.endswith(b'\n');assert H(raw)==r['provenance']['raw_sha256'];assert H(json.loads(raw)['statement'].encode())==r['provenance']['statement_sha256']
report['20_keys_and_raw_statement_bindings']=True
# Compare the independently printed n=3,4,5 source formulas with the recurrence determinant.
ns={'__file__':str(L/'scripts/billiard_check.py')};exec((L/'scripts/billiard_check.py').read_text().split('rows=[]')[0],ns)
x,R,B,DM=ns['x'],ns['R'],ns['B'],ns['DomainMatrix']
expect={3:x*x+12*x-12,4:3*x**3-2*x*x-12*x+8,5:x**6+420*x**5-1012*x**4+864*x**3+368*x*x-960*x+320}
for n,E in expect.items():
 m=(n-1)//2 if n%2 else n//2-1;shift=0 if n%2 else 1;A=[[B[i+j+2+shift] for j in range(m)] for i in range(m)];d=DM(A,(m,m),R.to_domain()).det();assert d.monic()==E.monic()
report['billiard_source_formulas_3_4_5']=True
# Check involution and invariant preservation in the modular implementation on sample Q rules.
ns={'__file__':str(L/'scripts/groups_check.py')};exec((L/'scripts/groups_check.py').read_text().split('def unbounded')[0],ns)
data=json.loads((L/'outputs/groups-check-0-13749.json').read_text());P=ns['P'];detpoly=ns['detpoly'];iv=ns['invol'];coeff=ns['coeff']
def ev(poly,x,y,t):return sum(c*pow(t,e,P)*pow(x,a,P)*pow(y,b,P) for (e,a,b),c in poly.items())%P
checks=0;sing=0
for row in data['rows'][::101]:
 T=row['T'];D=detpoly(T,list(range(4)))
 for theta in range(4):
  M=detpoly(T,[j for j in range(4) if j!=theta])
  for axis in range(2):
   x,y,t=7,11,5
   try:
    u,v=iv(D,M,axis,x,y,t);xx,yy=iv(D,M,axis,u,v,t);assert (xx,yy)==(x,y)
    assert (ev(D,u,v,t)*ev(M,x,y,t)-ev(D,x,y,t)*ev(M,u,v,t))%P==0;checks+=1
   except ZeroDivisionError:sing+=1
report['modular_involution_and_invariant_checks']={'passed':checks,'singular_skips':sing}
report['finite_scripts_all_exit_zero']={p.name:json.loads(p.read_text())['returncode'] for p in (L/'logs').glob('*.receipt.json')};assert all(v==0 for v in report['finite_scripts_all_exit_zero'].values())
(L/'outputs/validation.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
