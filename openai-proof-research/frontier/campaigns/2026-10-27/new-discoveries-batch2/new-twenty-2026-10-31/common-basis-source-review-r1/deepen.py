from pathlib import Path
import runpy,json
L=Path(__file__).resolve().parent;fetch=runpy.run_path(str(L/'fetch.py'))['fetch']
for name,url in [('larson.html','https://arxiv.org/html/2607.02208'),('lason-michalek.pdf','https://arxiv.org/pdf/1302.5236')]:fetch(name,url)
# Resolve remaining truncated computational subtrees, selecting the manuscript-backed Lean directories.
repo='openai/math';sha=json.loads((L/'receipts/openai-head.json').read_text())['sha'];root=json.loads(fetch('openai-lean-root.json','https://api.github.com/repos/'+repo+'/git/trees/'+sha+':lean'))
for e in root.get('tree',[]):
 if e['type']=='tree':
  d=json.loads(fetch('openai-lean-'+e['path']+'.json','https://api.github.com/repos/'+repo+'/git/trees/'+e['sha']+'?recursive=1'));print('LEAN',e['path'],d.get('truncated'),len(d.get('tree',[])),flush=True)
