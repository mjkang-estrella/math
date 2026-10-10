"""Discovery writer, never invoked by the read-only verifier."""
from pathlib import Path
import json,re,hashlib
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i90_anchored_rank_approximation'
domain=json.loads((ROOT/'frontier/sources/i88_nonlinear_banach_discovery/search-domain.json').read_text())
queries=[dict(name='rank',pattern=r'Auerbach|local.reflexiv|(?:finite.rank|low.rank|operator.rank).{0,70}(?:approxim|anchor|bound)|(?:approxim|anchor).{0,70}(?:finite.rank|operator.rank)'),dict(name='state',pattern=r'matched.walk|exceptional.direction|signed.measure|common.{0,20}(?:dominat|envelope)|(?:dominat|envelope).{0,40}(?:dimension|measure|rank)'),dict(name='entropy',pattern=r'(?:metric.entropy|covering.number|epsilon.net|\\varepsilon.net|\\epsilon.net).{0,90}(?:dimension|measure|rank)|(?:dimension|measure|rank).{0,90}(?:metric.entropy|covering.number|epsilon.net|\\varepsilon.net|\\epsilon.net)')]
summary=[]
for q in queries:
 pat=re.compile(q['pattern'],re.I);count=0;families={}
 with (S/('search-'+q['name']+'.jsonl')).open('w') as out:
  for rec in domain:
   for n,line in enumerate((ROOT/rec['local']).read_text(encoding='utf-8',errors='replace').splitlines(),1):
    if pat.search(line):
     out.write(json.dumps(dict(path=rec['path'],local=rec['local'],line=n,text=line),ensure_ascii=False)+'\n');count+=1;fam=rec['path'].split('/')[1];families[fam]=families.get(fam,0)+1
 q.update(records=count,manuscripts=len(families),flags='IGNORECASE')
 summary.append(dict(name=q['name'],families=sorted(families.items(),key=lambda x:(-x[1],x[0]))))
 print(q['name'],count,len(families),flush=True)
(S/'queries.json').write_text(json.dumps(queries,indent=2)+'\n');(S/'search-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
