from pathlib import Path
import json,re
D=Path(__file__).resolve().parents[1];s=D/'sources';r=json.loads((D/'reservation.json').read_text());tree=json.loads((s/'omega-tree.json').read_text());ids=list(map(str,r['ids']));hits=[]
for x in tree['tree']:
 p=x['path']
 if p.startswith(('D5/','Problems/')) and any(re.search(r'(?<!\d)'+i+r'(?!\d)',p) for i in ids):hits.append(x)
print('truncated',tree.get('truncated'),'entries',len(tree['tree']),'hits',hits)
report={'openai_HEAD':json.loads((s/'openai-head.json').read_text())['sha'],'omega_HEAD':json.loads((s/'omega-head.json').read_text())['sha'],'omega_recursive_tree_truncated':tree.get('truncated'),'omega_hits':hits,'scope':'Current complete recursive Omega path screen only, no proof bodies; OpenAI unchanged HEAD, inherited complete preprints listing reused. No semantic global novelty clearance.'}
(D/'outputs/registry-screen.json').write_text(json.dumps(report,indent=2)+'\n')
