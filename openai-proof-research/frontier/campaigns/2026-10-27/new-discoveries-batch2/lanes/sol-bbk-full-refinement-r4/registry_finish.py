#!/usr/bin/env python3
import retrieve,json
B=retrieve.B
try:
 t=json.loads((B/'sources/openai-lean-tree.json').read_text())
 for p in ['OAI','ComparatorChallenges']:
  e=next(x for x in t['tree'] if x['path']==p)
  d=retrieve.get('openai-lean-'+p+'-tree.json',f'https://api.github.com/repos/openai/math/git/trees/{e["sha"]}?recursive=1')
  if d:
   hits=[x for x in d['tree'] if any(y in x['path'].lower() for y in ['04014','372432','bachraoui','banerjee','bbk'])];print(p,'truncated',d.get('truncated'),'entries',len(d['tree']),'hits',hits)
  if d is None:break # stop on access/rate-limit failure
finally:
 (B/'retrieval-registry-finish.json').write_text(json.dumps(retrieve.records,indent=2))
 print([{k:v for k,v in r.items() if k in ['file','error','status']} for r in retrieve.records])
