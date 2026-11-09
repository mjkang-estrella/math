import sys
sys.dont_write_bytecode = True
import os, json, hashlib, shutil, collections
from pathlib import Path
HERE=Path(__file__).resolve().parent
OLD=HERE.parent/'codex'
root=HERE.parents[2]
allres=json.load(open(OLD/'results_t14112.json'))
budget=sorted(k for k,v in allres.items() if v['status']=='BUDGET')
mine=budget[::2]
assignment={'index_convention':'zero-based lexical sort of incoming BUDGET keys, even indices',
 'source_sha256':hashlib.sha256((OLD/'results_t14112.json').read_bytes()).hexdigest(),
 'source_budget_count':len(budget),'target32':['10|9,9,9,9','11|9,9,9'],
 'target14112':[{'index':i,'key':k} for i,k in enumerate(budget) if i%2==0]}
(HERE/'assignment.json').write_text(json.dumps(assignment,indent=2)+'\n')
for t,keys in [(14112,mine),(32,assignment['target32'])]:
 res=json.load(open(OLD/f'results_t{t}.json'))
 for k in keys:
  for j in res[k]['jobs']:
   src=OLD/j['file']
   if j['status']=='closed' and src.exists():
    dest=HERE/j['file'];dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dest)
 (HERE/f'incoming_t{t}.json').write_text(json.dumps({k:res[k] for k in keys},indent=1)+'\n')
notes=root/'notes/highdim_codex3a.md'
notes.write_text('# High-dimensional continuation: Codex 3a\n\n'
 'Scope: target 32 configurations `10|9,9,9,9` and `11|9,9,9`; '
 'and the 333 EVEN zero-based indices in the lexically sorted list of 665 '
 'incoming target-14112 BUDGET keys. No changes to codex3b.\n\n'
 '**COMPUTED** assignment source SHA-256: `'+assignment['source_sha256']+'`.\n\n'
 '## Exact target-14112 assignment\n\n'+
 '\n'.join('- '+str(x['index'])+': `'+x['key']+'`' for x in assignment['target14112'])+'\n\n'
 '## Method and validation requirements\n\n'
 'All certificates retain the existing nd format: prime kills and exact-size leaves. '
 'Unordered domains cover every distinct ordering at three or more far digits; '
 'smaller slices use all distinct ordered coefficient permutations. '
 'No certificate is accepted until checkhd.py and verification/v14_checknd_hd.py '
 'both pass when invoked directly as python3 -I -B, with no builtin monkeypatching. '
 'The -B option prevents bytecode writes outside this work area. '
 'Finite lengths below slice floors rely on the existing E/E2 enumeration through 600 digits.\n')
print('assigned',len(mine),'copied certs',len(list((HERE/'certs').rglob('*.jsonl'))))
print(collections.Counter(len(k.split('|')[1].split(',')) for k in mine))
