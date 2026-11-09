for a in ['2501.07098','2604.15138','2309.00989','2601.17325']:
 p=L/'sources'/ (a+'-html.txt')
 if not p.exists(): print(a,'NO HTML');continue
 s=read(p).decode(); print('SOURCE',a)
 if a in ['2604.15138','2501.07098']: print(s)
 else:
  for m in list(re.finditer('conjecture|concluding|Definition',s,re.I))[-5:]: print(s[max(0,m.start()-200):m.start()+2000])
print('ABS VERSIONS')
for p in sorted((L/'sources').glob('*abs.txt')):
 s=read(p).decode(); j=s.find('Submission history'); print(p.name,s[j:j+600]);
