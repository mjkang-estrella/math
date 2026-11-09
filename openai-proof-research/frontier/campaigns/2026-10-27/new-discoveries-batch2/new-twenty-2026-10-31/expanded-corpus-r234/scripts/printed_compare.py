import pathlib,json,itertools
D=pathlib.Path(__file__).resolve().parents[1];p=[tuple(x) for x in json.loads((D/'tour-certificate.json').read_text())['permutations_1based']]
def red(x):return tuple(sorted(x).index(a)+1 for a in x)
def arcs(t):return set(zip(t,t[1:]+t[:1]))
def variants(t):
 for rev in [False,True]:
  for comp in [False,True]:
   a=t[::-1] if rev else t
   if comp:a=[tuple(5-x for x in r) for r in a]
   yield a
# 1992 printed ordinary cycle; all its four-windows.
w=list(map(int,'123412534153214532413254'));c=[red((w+w)[i:i+4]) for i in range(24)]
rows=[tuple(map(int,x)) for x in '4231 3421 4312 4132 1324 2132 1431 4321 3213 3241 2314 2134 1231 2312 3123 1234 1243 1423'.split()]
blocks=[]
for r in rows:
 ties=[(a,b) for a in range(4) for b in range(a+1,4) if r[a]==r[b]]
 if not ties:blocks.append([[r]])
 else:
  a,b=ties[0];v=list(r);v[a]-=.1;v[b]+=.1;u=red(v);v[a]+=.2;v[b]-=.2;z=red(v);blocks.append([[u,z],[z,u]])
expand=[sum((list(b) for b in bs),[]) for bs in itertools.product(*blocks)]
res={}
for label,tt in [('1992 printed U4',[c]),('source Figure 17 twin-block expansions',expand)]:
 best=max(len(arcs(p)&arcs(v)) for t in tt for v in variants(t));res[label]={'expansions':len(tt),'maximum_common_directed_successor_pairs_under_rotation_reversal_complement':best,'total_pairs':24}
(D/'notes/printed-comparison.json').write_text(json.dumps(res,indent=2));print(json.dumps(res,indent=2))
