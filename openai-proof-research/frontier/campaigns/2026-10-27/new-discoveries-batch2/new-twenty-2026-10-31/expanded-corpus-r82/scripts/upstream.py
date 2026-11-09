from fetch import get,D
import json,subprocess
head=json.loads((D/'sources/openai-head.json').read_text())['sha'];j=json.loads((D.parent/'fresh-corpus-r10/sources/registry-preprints.json').read_text())
for term,key in [('A-PD4-group-without','pd4'),('Nonhomeomorphic-closed-aspherical','borel')]:
 paths=[e['path'] for e in j['tree'] if e['path'].startswith(term) and e['path'].count('/')==1 and e['path'].endswith('.pdf')]
 for p in paths:
  print(get((key+'.pdf','https://raw.githubusercontent.com/openai/math/'+head+'/preprints/'+p)),flush=True)
  subprocess.run(['pdftotext','-layout',str(D/'sources'/f'{key}.pdf'),str(D/'sources'/f'{key}.txt')])
