from audit import L,B,sha
import json,re
C=L/'copies'
selections={'corona.txt':[1,2,3,6,19], 'original-corona.txt':[3,4,5,10,11], 'zhu.txt':[1,2,5,6,7,8,9], 'brown.txt':[1,2,3,4], 'corona-companion.txt':[0,1,2,5,6,10,11,12,13], 'forest.txt':[0,1,2,15,16,17]}
coverage=[]
for name,pages in selections.items():
 p=C/'sources'/name; data=p.read_text();parts=data.split('\f');ranges=[]
 for i in pages:
  if i>=len(parts):continue
  start=sum(len(t)+1 for t in parts[:i]);ranges.append({'page_index':i,'char_start':start,'char_end':start+len(parts[i])})
  if name==__import__('sys').argv[2]: print('\nPAGE_INDEX',i,'\n',parts[i])
 coverage.append({'file':str(p),'sha256':sha(p.read_bytes()),'selection':ranges,'note':'zero-based form-feed pages, exact character ranges; only selection printed for requested file'})
(L/'body-coverage.json').write_text(json.dumps(coverage,indent=2)+'\n')
