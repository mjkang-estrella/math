import hashlib,json,math
from fractions import Fraction as F
from pathlib import Path
from datetime import datetime,timezone
root=Path(__file__).resolve().parent;lane=root.parent/'sol-fresh-source-discovery-r90'
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
manifest={p:h for h,p in (line.split(None,1) for line in (lane/'MANIFEST.sha256').read_text().splitlines())}
for p,h in manifest.items():assert sha(lane/p)==h,p
a=[9,8,7,6,5,4,3,4,5,6,7,8];d=[6-v for v in a]
assert sum(a)==72 and sum(d)==0 and min(a)>0
L=sum(F(abs(v),72) for v in d);assert L==F(1,4)
# Independently propagate the signed ROW vector through the integer matrix 60*C.
# Candidate uses column-vector propagation; this checks the orientation as well.
row=d[:];U=F(0);coefficient=F(1,72)
for k in range(161):
    U+=coefficient*sum(row)
    row=[60*row[(j-1)%12]-(60+a[j])*row[j] for j in range(12)]
    coefficient*=F(4,25*(k+1))
z=F(516,25)
E=L*z**161/math.factorial(161)/(1-z/162)
assert U+E < -F(1,25000)
frozen={str(p.relative_to(lane)):sha(p) for p in lane.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
(root/'review-freeze.json').write_text(json.dumps({'utc':datetime.now(timezone.utc).isoformat(),'source_lane':str(lane),'files':frozen},indent=2)+'\n')
record={'status':'PENDING_INDEPENDENT_REVIEW','credit':0,'counts':{'additional':8,'total':38},
 'manifest_verified':len(manifest),'frozen_files':len(frozen),'root_check':'Exact signed row Taylor sum through160 with absolute norm tail; U+E < -1/25000.',
 'U':str(U),'E':str(E),'root_read':'Full PROOF and discovery, cached actual publisher Conjecture3.9 and experimental criterion, He Section4.3 future question.',
 'math_assessment':'No ordinary gap identified. Uniformization is substochastic, all rates positive, cycle irreducible, stationary laws have correct orientation. Full universal stochastic order is refuted if source scope is as read.',
 'limits':'No independent review, Lean, paper or priority clearance. Generic exponential certification is uncredited. Closest historical Cox/MAP/MMPP counterexamples and routine-construction objection need review.',
 'proof_sha256':sha(lane/'PROOF.md')}
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'pass':True,'manifest':len(manifest),'frozen':len(frozen),'strict_gap':'< -1/25000','credit':0}))
