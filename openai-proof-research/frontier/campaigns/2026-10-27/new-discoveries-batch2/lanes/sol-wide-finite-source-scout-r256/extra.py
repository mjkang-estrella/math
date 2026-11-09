from retrieve import fetch,L
import hashlib,json,subprocess,re
hist=(L/'history-index.txt').read_text()
print('Early aliases',[(x,len(re.findall(x,hist,re.I))) for x in ['1603.05815','Mantica','question mark','1610.09165']])
for id in ['1603.05815v2','1610.09165v1']:
 fetch('https://arxiv.org/pdf/'+id,id+'.pdf')
 p=L/'sources'/(id+'.pdf')
 if p.exists():
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
  s=p.with_suffix('.txt').read_text()
  print(id,s[:1300])
  for m in list(re.finditer(r'(?m)^\s*(?:Conjecture|Theorem)\s+\d',s))[:4]:print(s[m.start():m.start()+1800])
