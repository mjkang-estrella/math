import json,hashlib,datetime
from pathlib import Path
import sympy as s
P=Path(__file__).resolve().parent;B=P.parent.parent;src=P.parent/'sol-fresh-source-discovery-r74';cwd=B.parents[4]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
prov=json.loads((src/'provenance.json').read_text())
manifest={v['path']:v['sha256'] for v in prov['manifest']}
bad=[name for name,h in manifest.items() if sha(src/name)!=h]
x=s.symbols('x',real=True);f=s.Function('f')(x)
ds=[s.diff(f,x,k) for k in range(5)]
expected=-ds[4]*f**3+4*ds[3]*ds[1]*f**2+3*ds[2]**2*f**2-12*ds[2]*ds[1]**2*f+6*ds[1]**4
assert s.simplify(-s.diff(s.log(f),x,4)*f**4-expected)==0
H=x**4+x**2-s.cos(10*x)/100
assert s.simplify(s.diff(H,x,2)-(12*x**2+2+s.cos(10*x)))==0
assert s.expand(12*(x-s.Rational(1,6))**2+s.Rational(2,3)-(12*x*x-4*x+1))==0
assert s.Rational(73,25)<3
frozen={str(f.relative_to(src)):sha(f) for f in sorted(src.rglob('*')) if f.is_file() and '__pycache__' not in f.parts}
result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'UNRESOLVED_PRESERVED','credit':0,'counts':[7,37],'scope':'Balabdaoui–Wellner2014 Conjecture3.1 sharp Chernoff curvature minimum at zero, not merely strong log-concavity.','gap':'Uniform Airy-specific fourth-log-derivative sign or compact cleared numerator sign remains unproved.','root_read':'Completed thread, SUMMARY and complete discovery.md; no fresh primary-body audit.','root_validation':'Four symbolic/rational identities pass: generic fourth-log derivative numerator, obstruction density curvature, completion of square, strict rational upper bound. No full Airy numerical or 3784-case worker replay.','manifest_entries':len(manifest),'manifest_mismatches':bad,'frozen_files':frozen,'limits':['Public weaker theorem already exists; sharper-family eligibility is unresolved.','No formal endpoint or source counterexample.','Worker freshness evidence historical; newer root17:20 inventories not used here for a target-specific absence claim.']}
result['root_failure']='Initial manifest reader assumed mapping; actual manifest is a list of path/hash records. StopIteration corrected without changing source files.'
(P/'ADOPTION.json').write_text(json.dumps(result,indent=2)+'\n')
nf=B/'NEXT.md';text=nf.read_text()
text=text.replace('and fresh analysis r74. No children. Do not equate Blueprint and Lean trees.','and fresh analysis r76. r74 sharp Chernoff curvature remains unresolved;\nits generic-density obstruction is not an Airy counterexample. Root handback\npreserves the public-weaker-theorem and sharper-family eligibility limits.\nNo children. Do not equate Blueprint and Lean trees.')
nf.write_text(text)
paths=[str(f.relative_to(cwd)) for folder in (src,P) for f in sorted(folder.rglob('*')) if f.is_file() and '__pycache__' not in f.parts and f.name!='pathspec.txt']
paths.append(str(nf.relative_to(cwd)));(P/'pathspec.txt').write_text('\n'.join(paths)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='frozen_files'}))
