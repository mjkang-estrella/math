from retrieve import *
import re
for ident in sys.argv[1:]:
 p=L/'sources'/(ident+'.txt');print('\n###',ident)
 if not p.exists():continue
 lines=p.read_text().splitlines();print('\n'.join(lines[:16]))
 for i,line in enumerate(lines):
  if re.search(r'^(Conjecture|Problem|Question)|we (conjecture|ask)|open problem|conjecture that',line.strip(),re.I):print('LINE',i+1,'\n','\n'.join(lines[max(0,i-2):i+24]))
 ix=next((i for i in range(len(lines)-1,-1,-1) if lines[i].strip().lower()=='references'),len(lines))
 print('END\n','\n'.join(lines[max(0,ix-45):ix]))
