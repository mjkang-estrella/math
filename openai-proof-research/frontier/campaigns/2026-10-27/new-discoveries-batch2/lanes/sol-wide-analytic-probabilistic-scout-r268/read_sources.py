from work import *
ids=['2210.12842v2','2203.14815v2','1612.00862v1','2001.09248v2','2101.10023v1','1509.06540v2','1102.2723v1','1511.03658v1','1801.07238v1','2007.04668v1','2104.11971v1','1511.01246v1','1708.02857v2','1501.05922v2']
if __name__=='__main__':
 for a in ids:
  p=L/'primary'/(a+'.pdf')
  if not p.exists():
   p=fetch('https://arxiv.org/pdf/'+a,a+'.pdf')
   if not p.exists():continue
   q=freeze(p)
   subprocess.run(['pdftotext','-layout',str(q),str(L/'science'/(a+'.txt'))],check=True,timeout=30)
  t=(L/'science'/(a+'.txt')).read_text()
  lines=t.splitlines();hit=[i for i,s in enumerate(lines) if any(w in s.lower() for w in ['conjecture','question','problem 1','theorem 1','theorem 2','open problem'])]
  print('\nSOURCE',a)
  for i in hit[:17]: print('\n'.join(lines[max(0,i-1):i+8]))
