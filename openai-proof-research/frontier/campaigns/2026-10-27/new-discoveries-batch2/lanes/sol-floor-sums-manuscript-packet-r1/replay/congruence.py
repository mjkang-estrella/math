from pathlib import Path
import json,re
L=Path(__file__).resolve().parent
N=[d.get('atom',tuple(d.get('args',[]))) for d in map(json.loads,(L/'frozen/sol-floor-sums-certificate-r2/dag.jsonl').open())]
inv={d['node']:d for d in json.loads((L/'assembly-inventory.json').read_text())}
defs={int(m[1]):m[2] for g in L.glob('Sem[0-9]*.lean') for m in re.finditer(r'^def e(\d+) .*? := (.*)$',g.read_text(),re.M)}
for f in sorted(L.glob('Dag*.lean')):
 if f.with_suffix('.olean').exists():continue
 s=f.read_text();parts=re.split(r'(?=theorem n\d+ )',s);out=[parts[0]]
 for p in parts[1:]:
  i=int(re.match(r'theorem n(\d+)',p)[1]);op=inv[i]['rule'];ds=N[i][1:-1];c=N[i][-1]
  if op=='monotonicity':
   cut=p.index('  simp only')
   tail='end\nend Assembly\n' if p.endswith('end\nend Assembly\n') else ''
   ids=[c,*N[c][1:]]
   names=list(dict.fromkeys([f'e{j}' for j in ids]+[f'p{j}' for j in ds]))
   changes=''.join(f'  change {defs[N[j][-1]]} at p{j}\n' for j in ds)
   p=p[:cut]+changes+'  simp only ['+', '.join(names)+']\n'+tail
  elif op=='trans' and '  simp only' in p:
   cut=p.index('  simp only');tail='end\nend Assembly\n' if p.endswith('end\nend Assembly\n') else ''
   typ='Iff' if '↔' in next(line for g in L.glob('Sem[0-9]*.lean') for line in g.read_text().splitlines() if line.startswith(f'def e{c} ')) else 'Eq'
   pr=f'p{ds[0]}'
   for j in ds[1:]:pr=f'({typ}.trans {pr} p{j})'
   p=p[:cut]+f'  exact {pr}\n'+tail
  out.append(p)
 f.write_text(''.join(out))
print('congruence and transitivity generation patched')
