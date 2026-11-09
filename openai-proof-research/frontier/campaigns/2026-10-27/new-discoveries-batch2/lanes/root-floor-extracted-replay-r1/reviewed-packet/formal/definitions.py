from pathlib import Path
import json,re
L=Path(__file__).resolve().parent
N=[d.get('atom',tuple(d.get('args',[]))) for d in map(json.loads,(L/'frozen/sol-floor-sums-certificate-r2/dag.jsonl').open())]
I={d['node']:d for d in json.loads((L/'assembly-inventory.json').read_text())}
for f in sorted(L.glob('Dag*.lean')):
 if f.with_suffix('.olean').exists():continue
 parts=re.split(r'(?=theorem n\d+ )',f.read_text());out=[parts[0]]
 for p in parts[1:]:
  i=int(re.match(r'theorem n(\d+)',p)[1]);op=I[i]['rule']
  if op=='intro-def':
   c=N[i][-1];condition=N[N[N[c][1]][1]][1]
   p=p.replace('  tauto\n',f'  by_cases hc : e{condition} _v <;> simp [hc]\n')
  out.append(p)
 f.write_text(''.join(out))
print('actual ite definition clauses patched')
