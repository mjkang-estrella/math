import sys
sys.argv.append('focus')
from research import P,get,sha
import json,re,urllib.parse
log=json.loads((P/'http.json').read_text());selected=[]
for row in log:
 if re.search('EvolutionAutomorphismMaximum|EvolutionSharpBound|SimpleEvolutionAutomorphismMaximum|EvolutionAutomorphismWeight',row['url']):selected.append(row)
(P/'registry-relevant.json').write_text(json.dumps(selected,indent=2))
for i,path in enumerate(['D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismMaximum.lean','D5/S3/QuadraticForms/EvolutionAlgebras/SimpleEvolutionAutomorphismMaximum.lean']):
 get(f'chronology-{i}.json','https://api.github.com/repos/the-omega-institute/trureturing/commits?sha=73a5033dd654a16a14fcd1b13277f1a03d81d826&per_page=1&path='+urllib.parse.quote(path))
# Strengthen the preinvestment report audit for the exact selected claim, without
# treating lexical absence as semantic clearance.
corpus=json.loads((P/'duplicate-corpus.json').read_text());out=[]
pat=re.compile(r'complex.{0,50}idempotent|unique.{0,35}idempotent|idempotent.{0,35}(count|spectr|number)|2610[.]22248|kaygorodov',re.I)
R=next(x for x in P.parents if x.name=='openai-proof-research')
for row in corpus:
 f=R/row['path'];lines=[{'line':i,'text':s[:2000]} for i,s in enumerate(f.read_text(errors='replace').splitlines(),1) if pat.search(s)]
 if lines:out.append({'path':row['path'],'hits':lines})
(P/'duplicate-focus.json').write_text(json.dumps({'pattern':pat.pattern,'files':len(corpus),'hits':out,'limit':'All-date lexical audit, not a proof of novelty.'},indent=2));print(json.dumps(out,indent=2)[:16000])
