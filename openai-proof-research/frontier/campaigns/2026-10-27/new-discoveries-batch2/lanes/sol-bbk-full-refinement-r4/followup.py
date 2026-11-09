#!/usr/bin/env python3
import retrieve,json
B=retrieve.B
# Resolve truncated Lean subtree rather than treating it as a complete absence screen.
r=json.loads((B/'sources/openai-root.json').read_text()); l=next(x for x in r['tree'] if x['path']=='lean')
t=None # prior shallow-tree HTTP failure; no retry
(B/'retrieval-followup.json').write_text(json.dumps(retrieve.records,indent=2))
print(retrieve.records)
for e in (t or {}).get('tree',[]):
 if e['type']=='tree':
  d=retrieve.get('openai-lean-'+e['path']+'-tree.json',f'https://api.github.com/repos/openai/math/git/trees/{e["sha"]}?recursive=1')
  print(e['path'],d.get('truncated'),len(d['tree']),[x['path'] for x in d['tree'] if any(y in x['path'].lower() for y in ['04014','372432','bachraoui','bbk'])])
retrieve.get('mathdb-current.html','https://mathdb.com/p/372432/nonnegativity-conjecture-for-the-q-binomial-quotient-g-k-n-q')
retrieve.get('chern-wang.html','https://arxiv.org/html/2601.19845v1')
# Source-bearing implementation dependencies of current formal registry hits.
h=json.loads((B/'sources/omega-head.json').read_text())['sha']
d=json.loads((B/'sources/omega-D5-tree.json').read_text())
for j,e in enumerate(x for x in d['tree'] if 'TwoColorPartition/' in x['path'] and x['path'].endswith('.lean')):
 retrieve.get('omega-implementation-'+str(j)+'.lean',f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{h}/D5/{e["path"]}')
(B/'retrieval-followup.json').write_text(json.dumps(retrieve.records,indent=2))
