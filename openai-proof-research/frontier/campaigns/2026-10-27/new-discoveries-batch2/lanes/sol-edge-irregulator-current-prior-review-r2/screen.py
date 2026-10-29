from pathlib import Path
import re,json
O=Path(__file__).resolve().parent
patterns={'target':r'irregul|bensmail|catherinot|fioravantes|marcille|oijid|2511[.-]14514','broad':r'edge.?delet|locally.?irreg|degree.?neighbor|neighbor.?degree|degree.?conflict|diamond|gadget|degree.?constrain|graph.?delet|irregular.?decomp','graph':r'graph|combinatorics|edgelabel|degree'}
results={}
for repo in ['omega','openai']:
 rows=[]
 with (O/'registry'/f'{repo}-tree.txt').open() as f:
  for line in f:
   path=line.rstrip().split('\t',1)[1]
   if re.search(patterns['target']+'|'+patterns['broad'],path,re.I): rows.append(path)
 results[repo]=rows
 (O/f'{repo}-broad-paths.txt').write_text('\n'.join(rows)+'\n')
# Catalog all graph-related result headings/abstract paragraphs and last result
text=(O/'registry/openai-CONTENTS.md').read_text()
paras=[p for p in text.split('\n\n') if re.search(r'graph|edge.?delet|locally.?irreg|neighbor.*degree|degree.*neighbor|diamond|gadget|373\.',p,re.I)]
(O/'openai-catalog-screen.txt').write_text('\n\n'.join(paras)+'\n')
(O/'screen.json').write_text(json.dumps({'patterns':patterns,'counts':{k:len(v) for k,v in results.items()}},indent=2))
print(json.dumps({k:len(v) for k,v in results.items()}))
for repo,rows in results.items():
 print(repo)
 for p in rows:
  if p.startswith(('D5/','Problems/','Library/','preprints/','lean/OAI/','lean/docs/')):print(p)
