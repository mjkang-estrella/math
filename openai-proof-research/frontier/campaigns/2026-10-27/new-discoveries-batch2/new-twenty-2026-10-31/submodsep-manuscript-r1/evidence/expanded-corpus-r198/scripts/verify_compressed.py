import pathlib,json,itertools,collections,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
z=json.loads((D/'outputs/submod-dual-compressed.json').read_text());coords=[tuple(s) for s in z['coords']];idx={s:i for i,s in enumerate(coords)}
maps=[[1<<idx[tuple(sorted(p[a] for a in s))] for s in coords] for p in itertools.permutations(range(5))]
F={sum((all(x>>a&1 for a in s))<<j for j,s in enumerate(coords)) for x in range(32)}
def act(x,p):return sum(p[j] for j in range(15) if x>>j&1)
balance=collections.Counter();goodweight=0
for a in z['support']:
 w=a['weight'];assert isinstance(w,int) and w>0
 if a['kind']=='submodular':
  (meet,cm),(join,cj),(x,cx),(y,cy)=a['terms'];assert (cm,cj,cx,cy)==(1,1,-1,-1);assert meet==x&y and join==x|y
  terms=a['terms']
 elif a['kind']=='good':assert a['point'] in F;goodweight+=w;terms=[(a['point'],1)]
 else:assert a['kind']=='bad' and a['point'] not in F;terms=[(a['point'],-1)]
 for p in maps:
  for x,c in terms:balance[act(x,p)]+=w*c
assert all(v==0 for v in balance.values());assert goodweight==z['denominator']
out={'verified':True,'source_parameters':{'d':5,'r':2,'n_including_empty':16},'support_rows':len(z['support']),'permutations':len(maps),'expanded_rows':120*len(z['support']),'distinct_points_in_balance':len(balance),'nonzero_balance_coefficients':sum(v!=0 for v in balance.values()),'good_weight':goodweight,'summed_upper_bound':-120*goodweight,'certificate_sha256':hashlib.sha256((D/'outputs/submod-dual-compressed.json').read_bytes()).hexdigest(),'method':'Independent expansion of every orbit row under all S5 coordinate permutations; integer coefficient cancellation; all sign classifications and meet/join identities checked directly. This is an ordinary exact certificate, not a Lean proof.'}
(D/'outputs/certificate-verification-compressed.json').write_text(json.dumps(out,indent=2));print(out)
