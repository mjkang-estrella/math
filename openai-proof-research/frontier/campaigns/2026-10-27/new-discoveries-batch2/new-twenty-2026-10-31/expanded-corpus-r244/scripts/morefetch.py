import json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];todo=[('https://arxiv.org/pdf/'+a,k) for a,k in [('2409.18195','mycielski-index-pdf'),('2006.03739','mycielski-number-pdf'),('2006.12826','circulants-proof-pdf'),('2104.03835','eternal-original-pdf')]]
todo += [('https://probxiv.com/problems/anti-van-der-waerden-numbers-on-graphs-2','aw-prior'),('https://iris.uniroma1.it/retrieve/941cd0c1-7c0c-4573-92c0-4f830dd75ef2/Ciliberti_A-deletion%E2%80%93contraction_2023.pdf','homology-followup-pdf')]
h=json.loads((D/'sources/openai-head/body').read_text())['sha'];todo.append(('https://api.github.com/repos/openai/math/git/trees/'+h,'openai-root'))
omega=json.loads((D/'sources/omega-tree/body').read_text());ids=list(json.loads((D/'extracted.json').read_text()))
for p in omega.get('tree',[]):
 path=p['path']
 if any(i in path for i in ids) and path.endswith(('.json','.md','.lean')):todo.append(('https://raw.githubusercontent.com/the-omega-institute/trureturing/'+omega['sha']+'/'+path,'omega-'+str(len(todo))))
(D/'fetch-followup.json').write_text(json.dumps(todo));print(todo)
