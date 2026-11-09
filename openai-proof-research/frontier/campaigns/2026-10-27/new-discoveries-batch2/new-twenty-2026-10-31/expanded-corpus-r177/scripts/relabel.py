import pathlib,sys,itertools,json
D=pathlib.Path(__file__).resolve().parents[1];sys.argv=[sys.argv[0],'3','1'];exec((D/'scripts/cover.py').read_text().split('for mask in range(')[0])
# abstract graph in interleaved original x1,y1,x2,y2,x3,y3 labels
original=[(0,1),(2,3),(4,5),(0,2),(2,4),(0,5)];rows=[]
for perm in itertools.permutations(range(6)):
 # perm gives assignment (x3,y3,x2,y2,x1,y1) -> original vertex
 inv={v:i for i,v in enumerate(perm)};E={frozenset((inv[a],inv[b])) for a,b in original}
 if not all(frozenset((ix(i),iy(i))) in E for i in range(n)):continue
 if any(frozenset((iy(i),iy(j))) in E for i in range(n) for j in range(i+1,n)):continue
 if any(frozenset((ix(i),iy(j))) in E for i in range(n) for j in range(i)):continue
 if any(frozenset((ix(i),iy(j))) in E and frozenset((ix(i),ix(j))) in E for i in range(n) for j in range(i+1,n)):continue
 if any(frozenset((z,ix(j))) in E and frozenset((iy(j),ix(k))) in E and frozenset((z,ix(k))) not in E for i,j,k in itertools.permutations(range(n),3) for z in [ix(i),iy(i)]):continue
 covers=[tuple(c>>v&1 for v in range(6)) for c in range(64) if c.bit_count()==3 and all(c>>a&1 or c>>b&1 for a,b in map(tuple,E))]
 gs={tuple(a+b for a,b in zip(g,h)) for g in covers for h in covers};ordered=sorted(gs,reverse=True);C,k=cols(ordered);fail=[]
 if C is None:fail.append(0)
 else:
  for hidx in range(1,7):
   hs={tuple(a+(v in s) for v,a in enumerate(g)) for g,co in zip(ordered,C) for s in itertools.combinations(co,hidx)}
   if hs and cols(sorted(hs,reverse=True))[0] is None:fail.append(hidx)
 rows.append({'permutation':perm,'failed_homological_indices':fail})
r={'admissible_labelings':len(rows),'all_pass':sum(not r['failed_homological_indices'] for r in rows),'rows':rows};(D/'outputs/cover-relabel.json').write_text(json.dumps(r,indent=2));print(r)
