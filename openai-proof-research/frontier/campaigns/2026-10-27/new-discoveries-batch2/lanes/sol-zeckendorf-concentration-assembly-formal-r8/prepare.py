from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
F=L/'frozen/sol-zeckendorf-cell-concentration-formal-r7'
for n in ['Inventory.lean','Audit.lean']:
 s=(F/n).read_text().replace('import Concentration','import Assembly')
 if n=='Inventory.lean':s=s.replace('modName == `Concentration)', 'modName == `Concentration || modName == `Assembly)')
 else:s=s.replace('`Tail, `Concentration]', '`Tail, `Concentration, `Assembly]')
 (L/n).write_text(s)
rows=json.loads((L/'freeze.json').read_text())
keep=[]
for r in rows:
 if Path(r['copy']).name.startswith('attempt-'):
  (L/r['copy']).unlink()
 else:keep.append(r)
(L/'freeze.json').write_text(json.dumps(keep,indent=2)+'\n')
s=(F/'certify.py').read_text()
start=s.index('def science():');end=s.index('def pins():')
s=s[:start]+'''def science():
    for r in json.loads((L/'freeze.json').read_text()):
        assert sha(Path(r['original']))==r['sha256']==sha(L/r['copy']),r
    for r in json.loads((L/'immutable-references.json').read_text()):
        assert sha(Path(r['original']))==r['sha256']==sha(Path(r['copy'])),r
    for n in ['Literal','Terminal','Law','Cells','Product','Prefix','Marks','Boards','Injection','Abundance','Tail','Concentration']:
        assert (L/(n+'.lean')).read_bytes()==(L/'frozen/sol-zeckendorf-cell-concentration-formal-r7'/(n+'.lean')).read_bytes()
'''+s[end:]
s=s.replace("'Tail','Concentration']", "'Tail','Concentration','Assembly']")
s=s.replace("'Tail', 'Concentration']", "'Tail', 'Concentration', 'Assembly']")
s=s.replace("'Concentration.lean','Inventory.lean'", "'Concentration.lean','Assembly.lean','Inventory.lean'")
s=s.replace("'provenance.json','bindings.json','immutable-references.json'", "'provenance.json','freeze.json','immutable-references.json'")
s=s.replace("'attempt-012.log'", "'attempt-013.log'").replace("'attempt-013.log').read_text(),names)", "'attempt-014.log').read_text(),names)")
s=s.replace('PARTIAL: actual length/parameters and generic thinning/atom bound CLOSED; generic concentration and mixture OPEN','CLOSED: finite Bernoulli interval and actual finite interval/tail; no asymptotics or mixing claim')
(L/'certify.py').write_text(s)
(L/'run.sh').write_text('''#!/bin/sh
set -eu
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
G=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
for n in Literal Terminal Law Cells Product Prefix Marks Boards Injection Abundance Tail Concentration Assembly; do
 python "$G" python runner.py -o "$n.olean" "$n.lean"
done
python "$G" python runner.py Inventory.lean
python "$G" python runner.py Audit.lean
''')
print('prepared certification')
