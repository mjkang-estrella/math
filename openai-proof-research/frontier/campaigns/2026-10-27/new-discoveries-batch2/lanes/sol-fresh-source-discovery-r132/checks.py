import sys,json,hashlib,time,math,subprocess
from pathlib import Path
L=Path(__file__).resolve().parent
def dump(n,x): (L/n).write_text(json.dumps(x,indent=2)+'\n')
if sys.argv[1]=='originals':
 import re,gzip
 hits=json.loads((L/'history-matches.json').read_text())
 hs={j['sha256']:j for j in hits}; aliases=[];orig={}
 with gzip.open(L/'history-aliases.jsonl.gz','rt') as f:
  for line in f:
   h,p=json.loads(line)
   if h not in hs:continue
   aliases.append([h,p])
   if re.search(r'(summary|discovery|proof|review|decision)[^/]*[.]md$',p,re.I):
    orig.setdefault(h,[]).append(p)
 dump('matching-aliases.json',aliases)
 dump('original-matching-dispositions.json',[dict(sha256=h,aliases=ps,excerpts=hs[h]['excerpts']) for h,ps in orig.items()])
 for h,ps in orig.items():print(ps[-1],len(ps))
 print('original bodies',len(orig),'all matching bodies',len(hits),'all matching aliases',len(aliases))
elif sys.argv[1]=='metadata':
 for n in ['omega','openai']:
  j=json.loads((L/'sources'/f'{n}-head.json').read_text())
  print(n,j['sha'],j['commit']['committer']['date'])
elif sys.argv[1]=='checks':
 # Exact route obstructions, not numerical evidence for the source conjecture.
 from fractions import Fraction as Q
 cases=[]
 for beta in [Q(1,4),Q(49,100),Q(1,2),Q(3,5),Q(3,4),Q(99,100)]:
  alpha=max(2*beta,2*beta*beta)
  cases.append(dict(beta=str(beta),wang_limiting_margin=str(1-alpha),positive=alpha<1))
 # A lazy two-state chain makes the rare-trap obstruction exact.
 # pi(rare)=d, P(rare,bulk)=a, P(bulk,rare)=ad/(1-d).
 # Dirichlet form=a*d*diff^2; Var=d(1-d)*diff^2.
 trap=[]
 for k in [4,8,16,32]:
  d=Q(1,2**k);a=Q(1,2**(2*k));gap=a/(1-d)
  assert d*a==(1-d)*(a*d/(1-d))
  assert d*(1-d)<=d # indicator variance absorbed by weak PI error d.
  trap.append(dict(k=k,rare_mass=str(d),spectral_gap=str(gap),rare_indicator_variance=str(d*(1-d))))
 # Dobrushin L1 control cannot be rescued by Gaussian sign cancellation.
 # E sum |beta*N(0,1/n)| = beta*(n-1)*sqrt(2/(pi*n)).
 rows=[dict(n=n,beta=.75,expected_abs_row_sum=.75*(n-1)*math.sqrt(2/(math.pi*n))) for n in [100,1000,10000]]
 # Exact pointwise obstruction, T has off-diagonal 3/5 and c=(1,1,1).
 # Realize by J_ij=atanh(3/5), h=-J*1, evaluated at x=1.
 lhs=6*Q(3,5);rhs=Q(1)*3
 assert lhs>rhs
 out=dict(scope='Checks of rejected proof routes only; no SK mixing proof or counterexample',wang_margin=cases,rare_trap=trap,dobrushin=rows,pointwise_obstruction=dict(aTa=str(lhs),sum_vi_di_squared=str(rhs),ratio=str(lhs/rhs)),passed=True)
 dump('check-results.json',out);print(json.dumps(out))
elif sys.argv[1]=='receipt':
 j=json.loads((L/'sources/omega-delta.json').read_text())
 rec={k:j.get(k) for k in ['status','ahead_by','total_commits']}
 rec.update(base=j['base_commit']['sha'],merge_base=j['merge_base_commit']['sha'],returned_commits=len(j['commits']),returned_files=len(j['files']),filenames=[f['filename'] for f in j['files']],cap_warning=len(j['files'])>=300 or len(j['commits'])>=250,semantic_clearance=False)
 dump('registry-delta-receipt.json',rec);print(json.dumps(rec))
