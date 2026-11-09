from pathlib import Path
import re
L=Path(__file__).resolve().parent
for name,pat in [('2408.08935v1','Question 3'),('2411.14661v1','BFPP|Proof of Theorem'),('2412.19338v1','Theorem 2.2|Proof of Theorem 2.2'),('2407.06321v1','3.2 Open Problem'),('2409.19768v1','Theorem 2.1')]:
 p=next((L/'frozen').glob('*-'+name+'.txt'));lines=p.read_text().splitlines();print('\nSOURCE',name)
 hits=[i for i,x in enumerate(lines) if re.search(pat,x)]
 for i in hits[:2]:print('\n'.join(f'{j+1}: {lines[j][:200]}' for j in range(max(0,i-3),min(len(lines),i+20))))
