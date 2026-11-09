from pathlib import Path
import json,re
L=Path(__file__).resolve().parent;D=L/'http';j=json.loads((L/'matched-plan.json').read_text());t=json.loads((L/'registry-final-screen.json').read_text())['pool-tree']['hits']
for x in t:
 j.append(['matched-pool-'+x['path'].replace('/','--'),'https://raw.githubusercontent.com/Vilin97/lean-pool/01db1d7049cf9668bda1e9e106875ee1278b43e6/'+x['path']])
j.extend([['bowtie-journal.pdf','https://www.global-sci.com/aam/article/download/8473/16877'],['gamma-journal.pdf','https://www.cambridge.org/core/services/aop-cambridge-core/content/view/1602209EF9ECEA0A9AB107A6F4079BCE/S2050509424000896a.pdf/two-sided-permutation-statistics-via-symmetric-functions.pdf']])
(L/'matched-full-plan.json').write_text(json.dumps(j))
