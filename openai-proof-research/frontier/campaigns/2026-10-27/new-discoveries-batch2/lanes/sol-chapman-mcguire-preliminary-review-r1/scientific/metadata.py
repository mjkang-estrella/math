from retrieve import *
for j in json.loads((L/'selected.json').read_text()):print(j['id'].split('/')[-1],'; '.join(j['authors']),j['published'],j['updated'])
# Read exact theorem and definition neighborhoods for compact rejection evidence.
import re
for ident in ['2002.01968v2','2102.01534v2']:
 lines=(L/'sources'/(ident+'.txt')).read_text().splitlines();print('\n',ident)
 for i,l in enumerate(lines):
  if re.search(r'^Theorem (6|1\.|2\.|3\.|1 |2 |3 )|C\(k, n\)|^Definition',l.strip()):print(i+1,'\n'.join(lines[max(i-2,0):i+22]))
