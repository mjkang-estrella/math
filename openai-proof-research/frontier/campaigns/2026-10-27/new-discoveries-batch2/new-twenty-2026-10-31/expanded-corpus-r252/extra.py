from pathlib import Path
import json
L=Path(__file__).resolve().parent
j=json.loads((L/'registry-jobs.json').read_text());j.append(['openai-root.json','https://api.github.com/repos/openai/math/git/trees/4eaee87548250b2682affda7d05d947c05554bae'])
for a in ['1602.00778','2407.05730','2605.28159','2609.09142','2610.02390']:
 j.extend([[a+'-abs.html','https://arxiv.org/abs/'+a],[a+'.pdf','https://arxiv.org/pdf/'+a]])
j.append(['adjacency-journal.pdf','https://doiserbia.nb.rs/ft.aspx?id=1452-86301500022E'])
(L/'extra-plan.json').write_text(json.dumps(j))
