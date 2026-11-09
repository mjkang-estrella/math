import pathlib,sys,itertools,json,time,random
D=pathlib.Path(__file__).resolve().parents[1];n=int(sys.argv[1]);ellmax=int(sys.argv[2]);sys.argv=[sys.argv[0],str(n),str(ellmax)];exec((D/'scripts/cover.py').read_text().split('for mask in range(')[0]);start=time.monotonic();rows=[];random.seed(177);count=0;bad=[];incomplete=False
masks=range(1<<len(opts)) if n<=4 else [random.getrandbits(len(opts)) for _ in range(4000)]
for mask in masks:
 if time.monotonic()-start>105:incomplete=True;break
 edges=base+[e for j,e in enumerate(opts) if mask>>j&1];E={frozenset(e) for e in edges}
 if any(frozenset((ix(i),iy(j))) in E and frozenset((ix(i),ix(j))) in E for i in range(n) for j in range(i+1,n)):continue
 if any(frozenset((z,ix(j))) in E and frozenset((iy(j),ix(k))) in E and frozenset((z,ix(k))) not in E for i,j,k in itertools.permutations(range(n),3) for z in [ix(i),iy(i)]):continue
 covers=[tuple(c>>v&1 for v in range(2*n)) for c in range(1<<2*n) if c.bit_count()==n and all(c>>a&1 or c>>b&1 for a,b in edges)]
 # certify all minimal covers have size n
 if any(all(c>>a&1 or c>>b&1 for a,b in edges) and not any(all((c^(1<<v))>>a&1 or (c^(1<<v))>>b&1 for a,b in edges) for v in range(2*n) if c>>v&1) for c in range(1<<2*n) if c.bit_count()!=n):continue
 valid+=1;gs={(0,)*(2*n)}
 for ell in range(1,ellmax+1):
  gs={tuple(a+b for a,b in zip(g,h)) for g in gs for h in covers};ordered=sorted(gs,reverse=True);C,k=cols(ordered)
  if C is None:continue
  for hidx in range(1,2*n+1):
   hs=sorted({tuple(a+(v in s) for v,a in enumerate(g)) for g,co in zip(ordered,C) for s in itertools.combinations(co,hidx)})
   if not hs:break
   count+=1;degree=n*ell+hidx
   # nonlinear first syzygy criterion; record only disconnected lcm interval.
   for i,g in enumerate(hs):
    for h in hs[i+1:]:
     if time.monotonic()-start>105:break
     l=tuple(max(a,b) for a,b in zip(g,h))
     if sum(l)<=degree+1:continue
     vs=[q for q in hs if all(a<=b for a,b in zip(q,l))];seen={g}
     while True:
      add={q for q in vs if q not in seen and any(sum(max(a,b) for a,b in zip(q,t))==degree+1 for t in seen)}
      if not add:break
      seen|=add
     if h not in seen:bad.append({'mask':mask,'ell':ell,'hidx':hidx,'g':g,'h':h,'all_hs':hs});break
    if bad:break
   if bad:break
  if bad:break
 if bad:break
r={'n_pairs':n,'ellmax':ellmax,'last_mask':mask,'CM_graphs':valid,'shift_ideals_checked':count,'nonlinear_first_syzygy':bad,'internal_time_stop':incomplete,'seconds':time.monotonic()-start};(D/f'outputs/cover-invariant{n}.json').write_text(json.dumps(r,indent=2));print(r)
