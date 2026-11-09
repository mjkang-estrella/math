from pathlib import Path
import json,re
L=Path(__file__).resolve().parent
N=[d.get('atom',tuple(d.get('args',[]))) for d in map(json.loads,(L/'frozen/sol-floor-sums-certificate-r2/dag.jsonl').open())]
def h(i):return N[i] if isinstance(N[i],str) else h(N[i][0])
def render(i):
 if isinstance(N[i],tuple) and h(i) in ['not','and','or']:
  a=N[i][1:]
  if h(i)=='not':return '(¬ '+render(a[0])+')'
  return '('+(' ∧ ' if h(i)=='and' else ' ∨ ').join(render(j) for j in a)+')'
 return f'(e{i} _v)'
for f in sorted(L.glob('Dag*.lean')):
 if f.with_suffix('.olean').exists():continue
 parts=re.split(r'(?=theorem n\d+ )',f.read_text());out=[parts[0]]
 for p in parts[1:]:
  i=int(re.match(r'theorem n(\d+)',p)[1])
  if h(i)=='lemma':p=re.sub(r'  change ¬ .* at hc',f'  change ¬ {render(N[i][-1])} at hc',p)
  out.append(p)
 f.write_text(''.join(out))
print('explicit classical discharge clauses patched')
