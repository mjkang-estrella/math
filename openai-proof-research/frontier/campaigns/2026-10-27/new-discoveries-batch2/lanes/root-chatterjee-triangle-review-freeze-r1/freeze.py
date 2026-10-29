from pathlib import Path
from fractions import Fraction as F
from datetime import datetime,timezone
import hashlib,json
root=Path(__file__).resolve().parent;lanes=root.parent;lane=lanes/'sol-fresh-source-discovery-r97'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((lane/'manifest.json').read_text())
for n,r in manifest.items():
    p=lane/n;assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],n
# Uniform-target identity: d(X,Y)=3 E|Y1-Y2| for conditionally iid copies.
# Average exact interval-pair distances directly over latent states.
def dist(intervals):
    total=F(0)
    for a,b in intervals:
        for c,d in intervals:
            if (a,b)==(c,d):v=(b-a)/3
            else:
                assert b<=c or d<=a
                v=abs((a+b-c-d)/2)
            total+=v
    return 3*total/len(intervals)**2
rows=[]
for n in range(2,15):
    intervals=lambda which,i,j: (F(i,n),F(i+1,n)) if which=='A' else ((F(n*i+j,n*n),F(n*i+j+1,n*n)) if which=='B' else (F(n*j+i,n*n),F(n*j+i+1,n*n)))
    values={}
    for X,Y in [('A','B'),('B','A'),('B','C'),('C','B'),('A','C'),('C','A')]:
        if X=='A':v=sum((dist([intervals(Y,i,j) for j in range(n)]) for i in range(n)),F(0))/n
        else:v=sum((dist([intervals(Y,i,j)]) for i in range(n) for j in range(n)),F(0))/(n*n)
        values[X+Y]=v
    r=F(1,n);expected={'AB':r,'BA':r,'BC':r*r,'CB':r*r,'AC':1-r*r+r**3,'CA':r}
    assert values==expected
    directed=values['AC']/(values['AB']+values['BC'])
    avg=(values['AC']+values['CA'])/(values['AB']+values['BA']+values['BC']+values['CB'])
    assert directed>F(n,4) and avg>F(n,4)
    rows.append({'n':n,'distances':{k:str(v) for k,v in values.items()},'directed_max_ratio':str(directed),'average_ratio':str(avg)})
files={str(p.relative_to(lane)):sha(p) for p in sorted(lane.rglob('*')) if p.is_file() and '__pycache__' not in p.parts and p.suffix!='.pyc'}
utc=datetime.now(timezone.utc).isoformat()
(root/'review-freeze.json').write_text(json.dumps({'utc':utc,'source_lane':str(lane),'files':files},indent=2)+'\n')
(root/'ADOPTION.json').write_text(json.dumps(dict(utc=utc,decision='FULL_ORDINARY_CANDIDATE_INDEPENDENT_REVIEW_REQUIRED',credit=0,counts=[8,38],manifest_files_verified=len(manifest),frozen_files=len(files),root_checks=rows,scope='Root read full proof/discovery, actual accepted-manuscript Section6 and Theorem2 context plus Fuchs–Wang Example2.5. Independently exact conditional-copy integration checks78distances and26ratios. No identified ordinary math gap; no formal PASS.',source='Uniform multiplicative interpretation of approximate triangle question for d,average,max distances. Section6 leaves approximate informal; preceding sourceTheorem2 includes both multiplicative and additive failure. Final publisher body unread; attribution needs review. No optimal additive-average claim.',eligibility='Serious routine modulo/shuffle adaptation objection; inspect actual object-specific prior constructions, sourceTheorem8 scope and full three-variable assembly. No priority/credit from missing printed endpoint alone.',next='Independent source/math/substantive/prior review before any Lean/paper.'),indent=2)+'\n')
print(json.dumps({'manifest':len(manifest),'freeze':len(files),'root_exact_checks':78,'ratios':26,'status':'PASS'}))
