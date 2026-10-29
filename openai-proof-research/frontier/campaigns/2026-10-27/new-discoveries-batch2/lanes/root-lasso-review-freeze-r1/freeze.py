from pathlib import Path
from fractions import Fraction as F
import hashlib,json,datetime
P=Path(__file__).resolve().parent;B=P.parent.parent;cwd=B.parents[4]
S=P.parent/'sol-fresh-source-discovery-r79'
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for c in iter(lambda:f.read(1048576),b''):h.update(c)
    return h.hexdigest()
manifest=json.loads((S/'SHA256.json').read_text())
bad=[n for n,h in manifest.items() if sha(S/n)!=h]
assert not bad,bad
c=F(-49999,100000);lam=F(1,20)
# Independent rational matrix inverse and Schur complement.
inv=[[1/(1-c*c),-c/(1-c*c)],[-c/(1-c*c),1/(1-c*c)]]
v=1-sum(c*inv[i][j]*c for i in range(2) for j in range(2))
z=[1,-1]
mean=[sum(inv[i][j]*z[j] for j in range(2)) for i in range(2)]
assert mean==[1/(1-c),-1/(1-c)]
assert sum(c*x for x in mean)==0
assert v==F(149999,2500050000) and 1+2*c==F(1,50000)
assert v<F(3,50000) and 1-v/lam**2>F(122,125)
assert 1-c*c>F(3,4)>F(17,20)**2
assert 0<(1+c)/(1-c)<1
x=F(4,5);assert F(3,8)*(x-x**3/6)>F(1,4)
assert F(223,71)>F(25,8) and F(22,7)<F(32,9)
def mul(a,b):
    out=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out
A=F(9,5)
assert [a/27 for a in mul(mul([A,-3],[A,-3]),[A,6])]==[A**3/27,0,-A,2]
assert F(61,250)-F(27,125)==F(7,250)
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
files={str(f.relative_to(S)):sha(f) for f in sorted(S.rglob('*')) if f.is_file() and '__pycache__' not in f.parts}
(P/'review-freeze.json').write_text(json.dumps({'utc':now,'source_lane':str(S),'files':files},indent=2)+'\n')
(P/'root-checks.json').write_text(json.dumps({'utc':now,'status':'PASS','scope':'Exact rational inverse, Schur complement, mixed-sign mean, threshold/CDF rational bounds and genuine expanded cubic identity only. No independent numerical CDF calculation or complete Gaussian formal certificate.','variance':str(v),'manifest_count':len(manifest),'all_frozen_files':len(files)},indent=2)+'\n')
(P/'ADOPTION.json').write_text(json.dumps({'utc':now,'status':'MATHEMATICAL_SEPARATION_CANDIDATE_REVIEW_PENDING','credit':0,'counts':[7,37],'root_read':'Complete SUMMARY/discovery and actual extracted source Lemma2 and Section3.2 conjecture/context.','holds':['VoR exact scope','ambiguous generally/fixed-lambda versus maximum-summary wording','closest thesis/comparison bodies','substantive classical-Lemma2 objection','bounded current-prior coverage','full literal Lean and later gates'],'root_reasoning':'Mixed-sign inactive mean cancels and Schur variance collapses near c=-1/2 while active block stays regular. Uniform orthogonal density/cubic bound is coherent. Numerical fixed-lambda failures already in source must not be recounted.','supremum_qualification':'Pointwise probability<27/125 yields supremum<=27/125; that suffices for strict separation. Do not infer strict supremum bound without attainment argument.','checker_qualification':'Worker cubic coefficient check directly assigned equal vectors; root instead multiplies factors independently. Other exact algebra checks pass.','review_lane':'sol-lasso-max-preliminary-review-r1'},indent=2)+'\n')
nf=B/'NEXT.md';t=nf.read_text()
t=t.replace('Active Sol high/default: edge-irregulator manuscript/packet r1,\nfresh analytic discovery r79 and fresh finite/arithmetic discovery r80.', 'r79 lasso yields an exact probability separation beating every orthogonal tuning\nparameter; source/general wording, closest-body and substantive holds remain.\nRoot rational KKT/Schur/cubic bounds pass; independent review pending, credit0.\nActive Sol high/default: edge-irregulator manuscript/packet r1,\nlasso preliminary review r1 and fresh finite/arithmetic discovery r80.')
nf.write_text(t)
paths=[]
for folder in (S,P):
    paths.extend(str(f.relative_to(cwd)) for f in sorted(folder.rglob('*')) if f.is_file() and '__pycache__' not in f.parts and f.name!='pathspec.txt')
paths.append(str(nf.relative_to(cwd)))
(P/'pathspec.txt').write_text('\n'.join(paths)+'\n')
print(json.dumps({'status':'PASS','freeze':len(files),'manifest':len(manifest),'variance':str(v)}))
