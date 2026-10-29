import hashlib,json
from pathlib import Path
from datetime import datetime,timezone
import sympy as S
root=Path(__file__).resolve().parent;lane=root.parent/'sol-fresh-source-discovery-r91'
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
manifest=json.loads((lane/'manifest.json').read_text())['sha256']
for p,h in manifest.items():assert sha(lane/p)==h,p
z,T,Q=S.symbols('z T Q');a=1+z;C=a*(T-Q)
Tp=z*T+a*(Q+C);Qp=a*Q+z*C;Cp=(z+z*z)*T+a*C
assert S.expand(Cp-a*(Tp-Qp))==0
M=S.Matrix([[a,a*z],[z,1+2*z]])
assert S.expand(M.trace()-(2+3*z))==0
assert S.expand(M.det()-(1+3*z+z*z-z**3))==0
def coeffs(p):return list(reversed(S.Poly(p,z).all_coeffs()))
p=1+z+z*z;e=1+4*z+z*z
P=coeffs(p);E=coeffs(e)
def get(v,k):return v[k] if 0<=k<len(v) else 0
for k in range(5):
    assert get(P,k)**2>=get(P,k-1)*get(P,k+1)
    assert get(E,k)**2>=get(E,k-1)*get(E,k+1)
    assert get(P,k)*get(E,k)>=max(get(P,k-1)*get(E,k+1),get(P,k+1)*get(E,k-1))
image=coeffs(S.expand(z*z*p+(1+2*z)*e))
assert image==[1,6,10,3,1] and image[3]**2<image[2]*image[4]
record={'utc':datetime.now(timezone.utc).isoformat(),'status':'UNRESOLVED','credit':0,'counts':{'additional':8,'total':38},
 'manifest_verified':len(manifest),'root_checks':'Symbolic invariant preservation, reduced trace/determinant, exact synchronized-input failure under reduced update.',
 'gap':'Uniform coefficient log-concavity for the literal initial orbit remains unproved; generic cone counterexamples are not source counterexamples.',
 'limits':'Root read full handoff, did not repeat n<=500 numerical evidence or independently clear full current prior art. Scope deviation /tmp/r91-search-tmp remains disclosed. No formal certificate or full ordinary proof.',
 'provenance_sha256':sha(lane/'provenance.json')}
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'pass':True,'manifest':len(manifest),'credit':0}))
