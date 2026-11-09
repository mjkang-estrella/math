import re,json,hashlib
from pathlib import Path
p=Path(__file__).resolve().parent
s=(p/'bodies/reversible2020.txt').read_text()
page=s.split('\f')[15]
pairs=[re.findall(r'(?<![01])[01]{35}(?![01])',l) for l in page.splitlines()]
pairs=[x for x in pairs if x]
assert len(pairs)==70 and all(len(x)==2 for x in pairs)
matrices=[[row[c] for row in pairs[start:start+35]] for start in (0,35) for c in (0,1)]
out=[]
for i,rows in enumerate(matrices):
    a=[[int(c) for c in row] for row in rows]
    orthogonal=all(sum(a[r][k]*a[t][k] for k in range(35))%2==(r==t) for r in range(35) for t in range(35))
    persymmetric=all(a[r][t]==a[34-t][34-r] for r in range(35) for t in range(35))
    assert orthogonal and persymmetric
    target=p/'bodies'/f'published-A{i+1}.txt'
    target.write_text('\n'.join(rows)+'\n')
    out.append(dict(matrix=i+1,rows=35,columns=35,orthogonal=orthogonal,persymmetric=persymmetric,generator='[I_35 | A]',code_length=70,code_dimension=35,reversal_cycles=35,full_automorphism_group_independently_recomputed=False,full_group_order_source='Theorem 5.1, p.15',sha256=hashlib.sha256(target.read_bytes()).hexdigest()))
(p/'matrix-validation.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
