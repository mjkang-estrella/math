import sys,json,hashlib,re,datetime,math
from pathlib import Path
from fractions import Fraction as Q
L=Path(__file__).resolve().parent; B=L.parents[1]; R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
if sys.argv[1]=='history':
 old=L.parent/'sol-fresh-source-discovery-r140/history-expanded.json'
 j=json.loads(old.read_bytes()); known={p:h for h,ps in j['aliases'].items() for p in ps}
 paths=set(known)
 for lane in (B/'lanes').iterdir():
  if lane==L or not lane.is_dir():continue
  for f in lane.iterdir():
   if f.is_file() and f.name.lower() in {'summary.md','discovery.md','proof.md','review.md','decision.md'}:paths.add(str(f.relative_to(R)))
 omit={'frozen','copy','inputs','input','evidence','extracted','replay','replays','build','payload','snapshots','private','verification','legacy-replay','fresh-replay','source'}
 patterns={
  'radon':r'Chan.{0,30}Kalai|Ter.Saakov|Gaussian.{0,30}(Radon|hull|intersection)|598-gaussian|00268|White.{0,20}conjecture',
  'krasniqi':r'2609[.]28707|Krasniqi|Alzer.Berg|boundary.contact|optimal Bernstein boundary',
  'selected':r'2610[.]37066|2211[.]17069|12220.023.01508|Mart.n.Go.i|Mart.n Go.i|Alonso.Guti.rrez|convolution bod|theta.convolution|θ.convolution'}
 hits={k:[] for k in patterns}; aliases={}; excluded=[]; changed=[]; missing=[]; reopen=[]
 for p in sorted(paths):
  if omit.intersection(Path(p).parts):excluded.append(p);continue
  f=R/p
  if not f.is_file():missing.append(p);continue
  b=f.read_bytes();h=sha(b);s=b.decode(errors='replace');aliases.setdefault(h,[]).append(p)
  if known.get(p)!=h:changed.append(p)
  matched=[k for k,pat in patterns.items() if re.search(pat,s,re.I)]
  if matched:
   # Reopen each matching original in full, separately from the screening read.
   b2=f.read_bytes();assert b2==b
   target=L/'reopened'/str(len(reopen));target.parent.mkdir(exist_ok=True);target.write_bytes(b2)
   reopen.append(dict(path=p,sha256=h,bytes=len(b2),copy=str(target.relative_to(L))))
   for k in matched:hits[k].append(p)
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
  s=(L/('context-'+n)).read_text()
  for k,pat in patterns.items():
   if re.search(pat,s,re.I):hits[k].append('context-'+n)
 save('history-receipt.json',dict(retained=str(old),retained_sha256=sha(old.read_bytes()),patterns=patterns,hits=hits,aliases=aliases,changed=changed,excluded_by_role=excluded,missing=missing,reopened=reopen,cutoff=None,full_bodies=True,limits='Lexical original report roles; no semantic absence, no new nested report discovery outside retained scope. r111-r113 originals retained; generated echoes excluded by role.'))
 print(json.dumps(dict(unique_bodies=len(aliases),paths=sum(map(len,aliases.values())),hits=hits,reopens=len(reopen),changed=len(changed)),indent=2))
elif sys.argv[1]=='checks':
 def integral(n,a,b,l=Q(0),r=Q(1)):
  return sum(Q(n*math.comb(n,k),n+k)*a**(n-k)*b**k*(r**(n+k)-l**(n+k)) for k in range(n+1))
 rows=[]
 for n in range(2,10):
  lo=Q(0);hi=Q(1);target=Q(1,2**n)
  for k in range(32):
   m=(lo+hi)/2
   if integral(n,1,-m)>target:lo=m
   else:hi=m
   if k not in [3,7,15,23,31]:continue
   b=lo;gap=integral(n,1,-b)-target;delta=gap/(2*n);v=1-b*(1-delta)
   mass=integral(n,1,-b,0,1-delta)+integral(n,v/delta,-v/delta,1-delta,1)
   assert gap>0 and 0<delta<1 and mass>target
   assert -v/delta<=-b
   rows.append(dict(n=n,b=str(b),beta_upper=str(hi),delta=str(delta),mass=str(mass),target=str(target)))
 # Exact n=2 source polynomial and rational enclosure.
 assert integral(2,1,Q(-4,5))==Q(19,75)
 # Log bounds from atanh series, z=1/3, to certify square comparison.
 z=Q(1,3);N=40
 log2lo=2*sum(z**(2*k+1)/Q(2*k+1) for k in range(N))
 log2hi=log2lo+2*z**(2*N+1)/((2*N+1)*(1-z*z))
 square_rows=[]
 for s in [Q(1,4),Q(1,2),Q(3,4)]:
  # Only dyadic s=1/4,1/2 have an exact log2 comparison here.
  if s==Q(3,4):continue
  theta=s*s;multiple=4 if s==Q(1,4) else 2
  upper=1-theta-theta*multiple*log2lo
  lower=1-theta-theta*multiple*log2hi
  simplex=Q(3,2)*(1-s)**2
  assert upper<simplex or lower>simplex
  square_rows.append(dict(s=str(s),square_squared_lower=str(lower),square_squared_upper=str(upper),simplex_squared=str(simplex),square_better=upper<simplex))
 assert square_rows[0]['square_better'] and not square_rows[1]['square_better']
 out=dict(status='PASS',endpoint_obstructions=rows,endpoint_cases=len(rows),square_certificates=square_rows,log2_bounds=[str(log2lo),str(log2hi)],scope='Exact finite rational diagnostics and elementary comparison certificates; no full geometric resolution.')
 save('checks.json',out);print('PASS',len(rows),'exact endpoint controls,',len(square_rows),'square comparisons')
elif sys.argv[1]=='context':
 out={}
 for n in ['ledger.json','prior-campaign-context.json']:
  p=L/('context-'+n);j=json.loads(p.read_bytes());out[n]=dict(sha256=sha(p.read_bytes()),keys=list(j),records={})
  for k,v in j.items():
   if isinstance(v,list):out[n]['records'][k]=v
 save('context-reading.json',out)
 print('Context full JSON parsed and all record bodies retained; selected alias scan in history-receipt.')
elif sys.argv[1]=='registry':
 pats=re.compile(r'convolution|martin.?goni|mart.n|brunn|shephard|covariogram',re.I);out=[]
 for n in ['omega-library-tree.json','omega-problems-tree.json','omega-docs-tree.json']:
  j=json.loads((L/'sources'/n).read_bytes());hits=[x for x in j['tree'] if pats.search(x['path'])];out.append(dict(file=n,truncated=j.get('truncated'),entries=len(j['tree']),hits=hits))
 save('registry-path-screen.json',out);print(json.dumps(out,indent=2))
