from audit import *
import re
before=json.loads((L/'mathlib-before.json').read_text())['files']
queries={'stable_words':r'(?i)\bstable\b|stablelaw|stable_distribution|stableMeasure|strong.?markov|levy.?process|lévy.?process', 'fractional_char':r'(?i)charFun|rpow|abs.*\^|\|.*\|.*\^', 'maximal':r'(?i)maximal|hasIndepIncrements|stationaryIncrements'}
out={}
for k,pat in queries.items():
 hits=[]
 for rel,h in before.items():
  if not rel.startswith('Mathlib/Probability/') and 'CharacteristicFunction/' not in rel:continue
  p=M/rel;assert sha(p)==h
  for n,line in enumerate(p.read_text().splitlines(),1):
   if re.search(pat,line):hits.append({'file':rel,'line':n,'text':line})
 out[k]=hits
dump('targeted-search.json',out)
print('stable terms',out['stable_words'])
# Extract bounded actual primary bodies for review, from already frozen text.
parts=[]
for name,a,b in [('primary__2608.17927v3.txt',65,185),('primary__2608.17927v3.txt',709,860),('primary__2608.17927v3.txt',918,937),('retrieval__0905.2626v4.txt',610,675)]:
 s=(L/'frozen'/name).read_text().splitlines();parts.append(name+f':{a}-{b}\n'+'\n'.join(s[a-1:b]))
(L/'primary-body-excerpts.txt').write_text('\n\n'.join(parts)+'\n')
print('primary excerpts written')
