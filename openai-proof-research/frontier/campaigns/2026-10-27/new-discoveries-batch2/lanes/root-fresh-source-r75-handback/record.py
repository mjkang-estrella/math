import json,hashlib,datetime
from pathlib import Path
P=Path(__file__).resolve().parent;B=P.parent.parent;cwd=B.parents[4];src=P.parent/'sol-fresh-source-discovery-r75'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1048576),b''):h.update(c)
 return h.hexdigest()
prov=json.loads((src/'provenance.json').read_text())
bad=[n for n,h in prov['files'].items() if sha(src/n)!=h['sha256']]
def mul(a,b):
 r=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):r[i+j]+=x*y
 return r
q=[1,2,4,7,11,13,17,19,20,20,22,20,21,21,21,20,22,20,20,19,17,13,11,7,4,2,1]
assert mul(q,mul([1]*2,[1]*3))==mul(mul(mul([1]*5,[1]*5),[1]*5),[1]*18)
assert q[10]>q[11]<q[12] and q==q[::-1]
F=[0,1]
for _ in range(15):F.append(F[-1]+F[-2])
def series(m,n,N):
 a=[1]+[0]*N
 for d in F[1:n+1]:
  for k in range(d,N+1):a[k]+=a[k-d]
 for d in F[m+1:m+n+1]:
  for k in range(N,d-1,-1):a[k]-=a[k-d]
 return a
v=series(5,5,8);assert v[8]-v[7]==12
L=sum(d for d in F[2:6] if 8%d==0)-sum(d for d in F[6:11] if 8%d==0);assert L==-5
a=series(2,5,16);first=[a[k]+(a[k-8] if k>=8 else 0) for k in range(17)]
b=series(1,6,0);assert first[16]-first[15]==-1 and b[0]==1
assert series(2,6,16)[16]-series(2,6,16)[15]==0
frozen={str(f.relative_to(src)):sha(f) for f in sorted(src.rglob('*')) if f.is_file() and '__pycache__' not in f.parts}
large=[{'path':str(f.relative_to(cwd)),'bytes':f.stat().st_size,'sha256':sha(f)} for f in src.rglob('*') if f.is_file() and f.stat().st_size>16*1024**2]
result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'UNRESOLVED_OLD_FAMILY_REVISIT','credit':0,'counts':[7,37],'root_read':'Full SUMMARY/discovery and actual old parent-qfib-r14 FINDINGS plus first-campaign pi-discrete-discovery-r2 heading.','root_exact_checks':'Generic symmetric quotient recomposition and strict valley; actual source (5,5) L8=-5 with delta8=12; (2,6) recurrence first summand -1 and compensation +1, total0.','gap':'Uniform all-parameter signed-denumerant positivity remains unproved.','selection_deviation':'Older first-campaign FINDINGS found only after investment; initial freshness classification invalid. Next delegate explicitly instructed to search all report names/all dates before selection, filenames first.','manifest_entries':len(prov['files']),'manifest_mismatches':bad,'all_file_hashes':frozen,'large_evidence_retained_locally_not_staged':large,'storage_note':'Oversized derived search transcript is preserved at original path with hash, omitted from git selection to avoid duplicating old campaign content in a giant log. No source bytes deleted.','worker_checks_not_root_replayed':True}
(P/'ADOPTION.json').write_text(json.dumps(result,indent=2)+'\n')
Q=P.parent/'root-silicosis-review-freeze-r1'
adopt={'utc':result['utc'],'status':'FULL_ORDINARY_CANDIDATE__REVIEW_PENDING','credit':0,'counts':[7,37],'root_read':'Complete PROOF/discovery/SUMMARY and accepted-manuscript conjecture text.','root_reasoning':'Finite bidiagonal coefficient transformation and strict-sign limiting quasiconcavity argument are coherent on inspection; root exact4665 finite cases corroborate algebra only. No full analytic/source or eligibility PASS yet.','strongest_objection':'Potential routine classical variation-diminishing/Descartes bridge; literal equality existence correction is excluded, surviving substantive multiplicity scope must be adjudicated.','holds':['independent math review','exact source/VoR correspondence','classical substantive eligibility','bounded current-prior screen','formal and later gates'],'review_lane':'sol-silicosis-multiplicity-preliminary-review-r1'}
(Q/'ADOPTION.json').write_text(json.dumps(adopt,indent=2)+'\n')
nf=B/'NEXT.md';text=nf.read_text()
text=text.replace('Active Sol high/default: edge-irregulator source formal r1, fresh finite/algebra r75,\nand fresh analysis r76.','r75 q-Fibonomial revisit remains unresolved; late first-campaign duplicate\nidentification invalidates its initial freshness claim. No credit.\nr76 supplies a complete ordinary silicosis multiplicity candidate, with\nclassical-subsumption/source-scope holds; independent review pending, credit0.\nActive Sol high/default: edge-irregulator source formal r1, fresh finite/algebra r77,\nand silicosis preliminary review r1.')
nf.write_text(text)
for n,out in ((75,P),(76,Q)):
 paths=[]
 for folder in (P.parent/f'sol-fresh-source-discovery-r{n}',out):
  paths += [str(f.relative_to(cwd)) for f in sorted(folder.rglob('*')) if f.is_file() and '__pycache__' not in f.parts and f.name!='pathspec.txt' and f.stat().st_size<=16*1024**2]
 if n==76:paths.append(str(nf.relative_to(cwd)))
 (out/'pathspec.txt').write_text('\n'.join(paths)+'\n')
print(json.dumps({'manifest':len(prov['files']),'mismatches':bad,'root_checks':'PASS','large_logs_retained_not_staged':large,'silicosis':'REVIEW_PENDING'}))
