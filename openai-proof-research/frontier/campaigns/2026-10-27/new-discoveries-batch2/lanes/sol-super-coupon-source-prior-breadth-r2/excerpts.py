from pathlib import Path
import re,json,subprocess,hashlib
L=Path(__file__).resolve().parent
for n in ['aldous-ch3']:
 subprocess.run(['pdftotext','-layout',str(L/'frozen-live'/(n+'.pdf')),str(L/'texts'/(n+'.txt'))],check=True)
out=[]
for f in sorted((L/'texts').glob('*.txt')):
 lines=f.read_text().splitlines(); starts=[]
 pats=[r'^Theorem [12][. ]',r'^Conjecture',r'^Proof[. ]',r'^Proof of Theorem']
 for pat in pats:
  ix=[i for i,t in enumerate(lines) if re.search(pat,t)]
  starts+=ix[:2]
 rows=[]
 for i in sorted(set(starts)):
  rows.append(dict(line=i+1,page=1+'\n'.join(lines[:i]).count('\f'),text='\n'.join(lines[max(0,i-2):i+45])))
 out.append(dict(file=f.name,sha256=hashlib.sha256(f.read_bytes()).hexdigest(),passages=rows))
(L/'body-coverage.json').write_text(json.dumps(out,indent=2)+'\n')
for row in out:
 if row['file'].startswith(tuple(__import__('sys').argv[1:])):
  print('\nFILE',row['file'])
  for p in row['passages']:print('LINE',p['line'],'PAGE',p['page'],'\n',p['text'])
