from pathlib import Path
import runpy,json
L=Path(__file__).resolve().parent;fetch=runpy.run_path(str(L/'fetch.py'))['fetch'];h=json.loads((L/'receipts/openai-head.json').read_text())['sha']
root=json.loads(fetch('openai-oai-root.json','https://api.github.com/repos/openai/math/git/trees/'+h+':lean/OAI'))
print([(e['path'],e['type']) for e in root.get('tree',[])],flush=True)
# Matched manuscript source bodies already read; obtain associated docs and fixed reference files.
t=json.loads((L/'receipts/openai-lean-docs.json').read_text())
for e in t.get('tree',[]):
 if e['type']=='blob':
  p=e['path']
  if any(n in p for n in ['114','085','171']):fetch('openai-doc-'+p.replace('/','__'),'https://raw.githubusercontent.com/openai/math/'+h+'/lean/docs/'+p)
