import pathlib,json,itertools,random,time
D=pathlib.Path(__file__).resolve().parents[1];B=set((D.parent/'expanded-corpus-r104/outputs/ssa5-best-set.txt').read_text().split());words=[''.join(w) for w in itertools.product('ACGT',repeat=5)];idx={w:i for i,w in enumerate(words)};rc=lambda w:w.translate(str.maketrans('ACGT','TGCA'))[::-1];pairs=[(i,idx[rc(w)]) for i,w in enumerate(words) if w<rc(w)];edge=[[idx[w[1:]+c] for c in 'ACGT'] for w in words];mask=[w in B for w in words]
def rho(m):
 ids=[i for i in range(1024) if m[i]];ee=[[j for j in edge[i] if m[j]] for i in ids];v=[1.0]*1024
 for _ in range(130):
  a=[0.0]*1024
  for i,e in zip(ids,ee):a[i]=sum(v[j] for j in e)
  r=max(a);v=[x/r for x in a]
 return r
base=rho(mask);best=base;improvements=[]
for a,b in pairs:
 mask[a]=not mask[a];mask[b]=not mask[b];r=rho(mask)
 if r>base+1e-9:improvements.append([words[a],words[b],r])
 best=max(best,r);mask[a]=not mask[a];mask[b]=not mask[b]
random.seed(20261102);random_best=base
for _ in range(80):
 ps=random.sample(pairs,2)
 for a,b in ps:mask[a]=not mask[a];mask[b]=not mask[b]
 random_best=max(random_best,rho(mask))
 for a,b in ps:mask[a]=not mask[a];mask[b]=not mask[b]
r=dict(base=base,single_flips=512,single_flip_best=best,single_flip_improvements=improvements,random_two_flips=80,random_two_best=random_best,verdict='numerical local screen only; true global optimum not determined; full space has 2^512 choices')
(D/'local-results.json').write_text(json.dumps(r,indent=2));print(r)
