import pathlib,sys,json,random,itertools
D=pathlib.Path(__file__).resolve().parents[1]
# Load definitions without executing the original experiment.
s=(D/'scripts/safe.py').read_text().split('out=[]\nfor n in range')[0];exec(compile(s,'safe-defs','exec'))
n=int(sys.argv[1]);cap=int(sys.argv[2]);total=nonbad=0;ps=[]
for a in patterns(n,cap):
 total+=1
 if len(set(a))<4:continue
 if not bad(a,6):
  nonbad+=1
  if not good(a,6):ps.append(a)
print('PATTERNS',n,cap,total,nonbad,len(ps),flush=True)
# Hash-bound the complete selected pattern list; sample at most1000 for disks.
(D/f'outputs/safe-patterns-{n}-{cap}.json').write_text(json.dumps(ps)+'\n')
if len(ps)>1000:ps=rng.sample(ps,1000)
checks=0
for extra in [2,4,8,12,20,30]:
 for rep in range(10):
  adj=graph(n,extra)
  for a in ps:
   checks+=1
   if not extends(adj,a,6):
    result={'n':n,'adj':[sorted(s) for s in adj],'boundary':a};(D/'outputs/safe-candidate.json').write_text(json.dumps(result));print('CANDIDATE',result,flush=True);raise SystemExit
 print('DISKS',extra,checks,flush=True)
o={'n':n,'max_boundary_colors':cap,'canonical_patterns_enumerated':total,'nonbad_using_at_least4':nonbad,'not_bad_not_good_patterns':len(json.loads((D/f'outputs/safe-patterns-{n}-{cap}.json').read_text())),'patterns_tested':len(ps),'disk_extension_tests':checks}
(D/f'outputs/safe-extended-{n}-{cap}.json').write_text(json.dumps(o,indent=2)+'\n');print(json.dumps(o),flush=True)
