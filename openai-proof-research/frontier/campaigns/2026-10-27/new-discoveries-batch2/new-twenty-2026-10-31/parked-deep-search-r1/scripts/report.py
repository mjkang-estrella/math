import sys,pathlib,json,hashlib,re,datetime
D=pathlib.Path(sys.argv[1]);out=D/'outputs'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def runs(pattern):
 result=[]
 for p in sorted((D/'logs').glob(pattern)):
  t=p.read_text();s=re.findall(r'^s (.*)',t,re.M);result.append(dict(log=str(p.relative_to(D)),status=s[-1] if s else 'see log',watchdog=re.findall(r'WATCHDOG[^\n]*',t)))
 return result
certs=[]
for p in sorted(out.glob('cube-*.check.json')):
 a=json.loads(p.read_text());stem=p.name.removesuffix('.check.json');a.update(case=stem,cnf_sha256=sha(out/(stem+'.cnf')),raw_proof_sha256=sha(out/(stem+'.lrat')));certs.append(a)
w=[]
for p in sorted(out.glob('divine-*.witness.json')):
 a=json.loads(p.read_text());a.pop('colors',None);a.update(file=str(p.relative_to(D)),sha256=sha(p));w.append(a)
raw=[]
for p in sorted(out.glob('cube*.lrat')):
 if '.trim.' in p.name:continue
 raw.append(dict(file=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=sha(p),complete_UNSAT=('s UNSATISFIABLE' in (D/'logs'/(p.stem+'.log')).read_text())))
res={
 '345754':dict(verdict='finite SAT witnesses, no refutation and no infinite proof',statement='There exists f:N->{-1,+1} such that for every d,k>=1, f(d)*sum(f(j*d),j=2..k)<=0.',source='https://arxiv.org/abs/2003.02887 Section 4.6 Conjecture 12',coverage=w,solver_runs=runs('divine-*.log'),credit=0,novelty='Source-known Liouville finite range; not a candidate',encoding='binary addition circuits count plus signs in each tail, guarded comparison for root sign; x1 fixed positive by global symmetry',discarded='divine-1024.invalid.* used a missing-tail-term prototype; excluded from all conclusions'),
 '340618':dict(verdict='partial n=5 certified finite cases; whole n=5 NOT settled',statement='For each n>=2 and M, the minimum ordered Schur-triple count in Z/(2^n) at cardinality M is attained by a centered set.',source='https://arxiv.org/abs/1810.01225 Conjecture 1.7',certified_cases=certs,other_raw_proofs=raw,solver_runs=runs('cube*.log'),credit=0,novelty='Only parameter cases, no whole-conjecture resolution; no Lean endpoint',encoding='32 primary membership variables; exact cardinality via binary full-adders; one AND variable per distinct unordered support of a Schur triple, repeated with ordered multiplicity; strict bound below exhaustive centered minimum; no symmetry breaking',complement_encoding='ST(A)=1024-96*b+3*b*b-ST(B), B=Z32\\A and b=32-M; follows inclusion-exclusion over ordered x,y and z=x+y',remaining='M=18..26 unsearched; source already handles M<=17; any incomplete or unchecked proof explicitly excluded from certified cases')}
(D/'results.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps(dict(certified_cases=[x['case'] for x in certs],witnesses=w),indent=2))
