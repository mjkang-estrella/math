import hashlib,json,math
from fractions import Fraction as Q
from pathlib import Path
from datetime import datetime,timezone
root=Path(__file__).resolve().parent;lane=root.parent/'sol-fresh-source-discovery-r88'
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
manifest=json.loads((lane/'provenance.json').read_text())['manifest_sha256']
for p,h in manifest.items():assert sha(lane/p)==h,p
count=0
for m in (2,3,8):
    for n in range(9):
        for k in (0,1,4,13):
            for c in (0,1):
                q=math.prod(k+j for j in range(1,n+1))*math.prod(m*(k+n+c)-j for j in range(n))
                literal=(Q(math.comb(n+k+1,k)*math.comb(m*(n+k+1),n),n+k+1) if c else Q(math.comb(n+k,k)*math.comb(m*(n+k),n)))
                assert literal==Q(q,math.factorial(n)*math.factorial(n+c))
                count+=1
T=[[math.comb(n,k)*math.comb(2*n,n-k) if k<=n else 0 for k in range(4)] for n in range(4)]
P=[]
for i in range(3):
    P.append([T[i+1][j]-sum(T[i][k]*P[k][j] for k in range(i)) for j in range(4)])
assert P[2]==[-8,-9,10,1]
record={'utc':datetime.now(timezone.utc).isoformat(),'status':'UNRESOLVED','credit':0,'counts':{'additional':8,'total':38},
 'manifest_verified':len(manifest),'root_checks':{'collocation_identities':count,'production_row_2':P[2]},
 'gap':'All finite minors of four triangles and strict positivity of both square collocation kernels remain unproved.',
 'limits':'Root read full handoff and independently checked finite algebraic identities only, not all worker minors or a universal positivity statement. Two closest successor bodies and semantic current-prior clearance remain HOLD. Negative production entries do not refute the source.',
 'provenance_sha256':sha(lane/'provenance.json')}
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'pass':True,'hashes':len(manifest),'identities':count,'credit':0}))
