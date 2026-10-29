import hashlib,json,math
from pathlib import Path
from datetime import datetime,timezone
root=Path(__file__).resolve().parent;lane=root.parent/'sol-fresh-source-discovery-r89'
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
manifest=json.loads((lane/'manifest.json').read_text())['sha256']
for p,h in manifest.items():assert sha(lane/p)==h,p
primes=[p for p in range(3,80,2) if all(p%d for d in range(2,math.isqrt(p)+1))]
checks=0
for s in range(3,36):
    for p in primes:
        counts=[[0]*p for _ in range(p)]
        for x in range(-s,s+1):
            for y in range(-s+abs(x),s-abs(x)+1): counts[x%p][y%p]+=1
        q,r=divmod(2*s+1,p)
        expected=q*q//2 if q%2==0 else (q*q+(1 if r==p-1 else -1))//2
        assert min(map(min,counts))==expected
        if r:assert p*p*expected<=2*s*s
        else:assert p*p*expected==((2*s+1)**2-p*p)//2
        checks+=1
allfiles={str(p.relative_to(lane)):sha(p) for p in lane.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
freeze={'utc':datetime.now(timezone.utc).isoformat(),'source_lane':str(lane),'files':allfiles}
(root/'review-freeze.json').write_text(json.dumps(freeze,indent=2)+'\n')
record={'status':'PENDING_INDEPENDENT_REVIEW','credit':0,'counts':{'additional':8,'total':38},
 'manifest_verified':len(manifest),'frozen_files':len(allfiles),'root_exact_fiber_cases':checks,
 'root_read':'Entire PROOF, SUMMARY, discovery; published Conjecture1.6, lower-construction proofs and Theorem3.2 counting argument.',
 'math_assessment':'No gap found in root ordinary reading. Noncyclic rank-two quotient gives F_p^2 with generator images a basis; same-parity square counting gives all branches, including q=0 and unique short progression. Source provides attainment.',
 'strongest_objection':'Potentially routine two-coordinate refinement of source one-coordinate counting plus elementary rank-two quotient structure. Full intended endpoint is covered, but this does not by itself establish substantive eligibility.',
 'limits':'No Lean, paper, independent math PASS or current-priority clearance. Root finite tests check transcription, not universal proof; worker HNF tests not rerun.',
 'proof_sha256':sha(lane/'PROOF.md')}
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'pass':True,'manifest':len(manifest),'frozen':len(allfiles),'fiber_cases':checks}))
