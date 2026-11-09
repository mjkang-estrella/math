import json,itertools
from pathlib import Path
D=Path(__file__).resolve().parents[1];o=json.loads((D/'outputs/code-counterexample.json').read_text());rows=o['rows'];C={0}
for r in rows:C|={c^r for c in list(C)}
assert len(C)==64
assert all(x^y in C for x in C for y in C)
sig=[tuple(sum((x>>i)&1 for x in C if x.bit_count()==w) for w in range(13)) for i in range(12)]
assert all((sig[i]==sig[j])==(i//2==j//2) for i in range(12) for j in range(12))
# Explicit witness rejecting each nonconstant partial pair swap, independently of search routine.
cert=[]
for mask in range(64):
 def act(x):
  y=0
  for i in range(12):y|=((x>>i)&1)<<(i^(1 if mask>>(i//2)&1 else 0))
  return y
 bad=next((r for r in rows if act(r) not in C),None)
 cert.append({'mask':mask,'rejecting_generator':bad,'image':act(bad) if bad is not None else None})
 assert (bad is None)==(mask in [0,63])
print('rows as coordinates 0..11:',*[format(x,'012b')[::-1] for x in rows],sep='\n')
print('Codewords',sorted(C));print('weight signatures',sig);print('closure checked',4096,'ordered pairs');print('rejected swaps',json.dumps(cert,indent=2))
(D/'outputs/code-independent-check.json').write_text(json.dumps(dict(codewords=sorted(C),pair_swap_witnesses=cert,signatures=sig,closure_ordered_pairs=4096),indent=2)+'\n')
