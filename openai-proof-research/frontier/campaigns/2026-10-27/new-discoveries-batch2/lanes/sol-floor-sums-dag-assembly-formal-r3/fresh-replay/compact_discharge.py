from pathlib import Path
import json,re,shutil
L=Path(__file__).resolve().parent
N=[d.get('atom',tuple(d.get('args',[]))) for d in map(json.loads,(L/'frozen/sol-floor-sums-certificate-r2/dag.jsonl').open())]
I={d['node']:d for d in json.loads((L/'assembly-inventory.json').read_text())}
def head(i):return N[i] if isinstance(N[i],str) else head(N[i][0])
for f in sorted(list(L.glob('Dag*.lean'))+list((L/'parts').glob('*.lean'))):
 if f.with_suffix('.olean').exists():continue
 parts=re.split(r'(?=theorem n\d+ )',f.read_text());out=[parts[0]];changed=False
 for p in parts[1:]:
  i=int(re.match(r'theorem n(\d+)',p)[1]);d=I[i]
  if d['rule']=='lemma':
   c=N[i][-1];clause=list(N[c][1:]) if head(c)=='or' else [c]
   for h in d['discharged']:
    candidates=[(k,q) for k,q in enumerate(clause) if (isinstance(N[q],tuple) and head(q)=='not' and N[q][1]==h) or (isinstance(N[h],tuple) and head(h)=='not' and N[h][1]==q)]
    k,q=candidates[0];pr='hn'
    if k<len(clause)-1:pr=f'(Or.inl {pr})'
    for _ in range(k):pr=f'(Or.inr {pr})'
    body=f'Classical.byContradiction (fun hn => hc {pr})' if isinstance(N[q],tuple) and head(q)=='not' and N[q][1]==h else f'(fun hn => hc {pr})'
    pattern=rf'  have h{h} : .*? := by\n(?:    .*\n)+'
    p,count=re.subn(pattern,f'  have h{h} : (e{h} _v) := {body}\n',p,count=1)
    if count:changed=True
    else:assert f'  have h{h} : (e{h} _v) :=' in p,(f,h)
  out.append(p)
 if changed:
  dest=L/'attempts/compact-discharge'/f.relative_to(L);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,dest)
  f.write_text(''.join(out))
print('compact kernel-checked clause injections generated')
