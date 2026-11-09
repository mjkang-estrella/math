import os, resource, re, json
from pathlib import Path
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
l=Path(__file__).parent
for f in sorted((l/'sources').glob('*-abs')):
 s=f.read_text();vs=sorted(set(re.findall(r'/abs/[0-9.]+v(\d+)',s)));print(f.name,'versions',vs,'journal',re.findall(r'<td class="tablecell jref">(.*?)</td>',s,re.S))
for a in ['0809.2551','0812.3082','0912.2916','0801.0939','0810.3892','0805.0392']:
 s=(l/'sources'/(a+'-pdf.txt')).read_text();lines=s.splitlines();print('\nSOURCE',a)
 if a in ['0809.2551','0812.3082']:print(s)
 else:
  inds=set()
  for j,line in enumerate(lines):
   if re.search('[Cc]onjecture',line):inds.update(range(max(0,j-8),min(len(lines),j+18)))
  print('\n'.join(f'{j+1}: {lines[j]}' for j in sorted(inds)))
