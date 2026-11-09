from pathlib import Path
import re,json
L=Path(__file__).resolve().parent
jobs=[];history={}
for p in (L/'http').glob('*.abs.html'):
 aid=p.name.split('.abs')[0];s=p.read_text();vs=sorted(set(re.findall(r'\[v(\d+)\]',s)),key=int);history[aid]=vs
 for v in vs:
  jobs.append([aid+'v'+v+'.pdf','https://arxiv.org/pdf/'+aid+'v'+v])
h=json.loads((L/'http/openai-head.json').read_text())['sha']
jobs.extend([['openai-current-CONTENTS.md',f'https://raw.githubusercontent.com/openai/math/{h}/CONTENTS.md'],['nath-proof.pdf','https://arxiv.org/pdf/2305.15899'],['beck-leon.pdf','https://arxiv.org/pdf/1804.00208'],['potts-followup.pdf','https://arxiv.org/pdf/1801.07547'],['parker.pdf','https://arxiv.org/pdf/2406.06501']])
(L/'version-history.json').write_text(json.dumps(history,indent=2));(L/'version-jobs.json').write_text(json.dumps(jobs));print(history)
