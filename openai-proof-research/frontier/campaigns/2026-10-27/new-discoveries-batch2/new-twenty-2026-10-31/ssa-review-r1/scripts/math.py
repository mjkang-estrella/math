import pathlib,json,itertools,fractions,decimal
D=pathlib.Path(__file__).resolve().parents[1];S=D.parent/'expanded-corpus-r104';j=json.loads((S/'outputs/ssa5-certificate.json').read_text()); W=[''.join(t) for t in itertools.product('ACGT',repeat=5)]
rc=lambda w:w.translate(str.maketrans('ACGT','TGCA'))[::-1]
swap=lambda w:w.translate(str.maketrans('AT','TA'))
T={w for w in W if sum(c in 'TC' for c in w)>=3}; B=set((S/'outputs/ssa5-best-set.txt').read_text().split());assert B==set(j['S'])
rem=json.loads((S/'outputs/ssa5-structure.json').read_text())['tc_orientation']['removed_TC_words'];source=(T-set(rem))|{rc(w) for w in rem}
assert {swap(w) for w in B}==source
assert all(swap(rc(w))==rc(swap(w)) for w in W)
assert all((w in X)!=(rc(w) in X) for X in [T,B] for w in W)
lo=[400*sum(j['v'].get(w[1:]+c,0) for c in 'ACGT')-1299*j['v'][w] for w in B]
up=[649*j['u'][w]-200*sum(j['u'].get(w[1:]+c,0) for c in 'ACGT') for w in T]
assert min(lo)>=0 and min(up)>=0 and min(j['u'].values())>0 and max(j['v'].values())>0
# Mutate the lower witness entry until its outgoing sum cannot support it.
v=dict(j['v']);v['TTACA']=10**20
bad=[w for w in B if 1299*v[w]>400*sum(v.get(w[1:]+c,0) for c in 'ACGT')];assert bad
out={'symmetry_and_pairing':'passed','certificates':{'lower_min_slack':min(lo),'upper_min_slack':min(up)},'negative_mutation_failures':bad,'spectra':{},'counts':{}}
F=fractions.Fraction;decimal.getcontext().prec=60
fmt=lambda x:str(decimal.Decimal(x.numerator)/decimal.Decimal(x.denominator))
for name,X in [('TC',T),('S5',B)]:
 words=sorted(X);idx={w:i for i,w in enumerate(words)};edges=[[idx[z] for c in 'ACGT' if (z:=w[1:]+c) in X] for w in words]
 rows=[i for i,e in enumerate(edges) for _ in e];cols=[z for e in edges for z in e];lab=[-1]*512;order=[];seen=set()
 def dfs(i):
  if i in seen:return
  seen.add(i)
  for z in edges[i]:dfs(z)
  order.append(i)
 for i in range(512):dfs(i)
 rev=[[] for _ in range(512)]
 for i,e in enumerate(edges):
  for z in e:rev[z].append(i)
 def assign(i,k):
  if lab[i]>=0:return
  lab[i]=k
  for z in rev[i]:assign(z,k)
 nc=0
 for i in reversed(order):
  if lab[i]<0:assign(i,nc);nc+=1
 bounds=[]
 for k in range(nc):
  ids=[i for i in range(512) if lab[i]==k];ii={i:t for t,i in enumerate(ids)};ee=[[ii[z] for z in edges[i] if z in ii] for i in ids]
  if not any(ee):bounds.append((F(0),F(0),len(ids)));continue
  vec=[1]*len(ids)
  for _ in range(1400): vec=[sum(vec[z] for z in e) for e in ee]
  av=[sum(vec[z] for z in e) for e in ee];rat=[F(a,v) for a,v in zip(av,vec)];bounds.append((min(rat),max(rat),len(ids)))
 lower=max(a for a,b,n in bounds);upper=max(b for a,b,n in bounds)
 out['spectra'][name]={'rho_lower':fmt(lower),'rho_upper':fmt(upper),'scc_sizes':sorted([n for a,b,n in bounds],reverse=True),'exact_lower':[str(lower.numerator),str(lower.denominator)],'exact_upper':[str(upper.numerator),str(upper.denominator)],'rate_mid':str(((decimal.Decimal(fmt(lower))+decimal.Decimal(fmt(upper)))/2).ln()/decimal.Decimal(2).ln())}
 count=[1]*512;counts={5:512}
 for n in range(6,61):
  count=[sum(count[z] for z in e) for e in edges];counts[n]=sum(count)
 out['counts'][name]=counts
 for n in [5,6,7,8]:
  direct=sum(all(w[i:i+5] in X for i in range(n-4)) for tup in itertools.product('ACGT',repeat=n) if (w:=''.join(tup)))
  assert direct==counts[n]
assert decimal.Decimal(out['spectra']['S5']['rho_lower'])>decimal.Decimal(out['spectra']['TC']['rho_upper'])
out['TC_not_beaten_by_itself']=True
(D/'math-results.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items() if k not in ['counts','spectra']},indent=2));print({k:{x:v for x,v in a.items() if not x.startswith('exact')} for k,a in out['spectra'].items()})
