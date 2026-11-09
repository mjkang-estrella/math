from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
refs=json.loads((L/'inherited/immutable-references.json').read_text())
for r in refs:
 for key in ['original','copy']:
  assert hashlib.sha256(Path(r[key]).read_bytes()).hexdigest()==r['sha256']
(L/'immutable-references.json').write_text(json.dumps(refs,indent=2)+'\n')
s=(L/'inherited/certify.py').read_text()
start=s.index('    for r in json.loads((L/\'source-bindings.json\').read_text()):')
end=s.index('def pins():')
s=s[:start]+'''    for r in json.loads((L/'bindings.json').read_text()):
        assert sha(L/r['copy'])==r['sha256'],r
        if not r['administrative']:assert sha(Path(r['original']))==r['sha256'],r
    for r in json.loads((L/'immutable-references.json').read_text()):
        assert sha(Path(r['original']))==r['sha256']==sha(Path(r['copy'])),r
    for n in ['Literal','Terminal','Law','Cells','Product','Prefix','Marks','Boards','Injection','Abundance','Tail']:
        assert (L/(n+'.lean')).read_bytes()==(L/'inherited'/(n+'.lean')).read_bytes()
'''+s[end:]
s=s.replace("'Abundance','Tail']", "'Abundance','Tail','Concentration']")
s=s.replace("'Abundance', 'Tail']", "'Abundance', 'Tail', 'Concentration']")
s=s.replace("'Tail.lean','Inventory.lean'", "'Tail.lean','Concentration.lean','Inventory.lean'")
s=s.replace("'source-bindings.json'", "'bindings.json'")
s=s.replace("'attempt-011.log'", "'attempt-012.log'").replace("'attempt-012.log').read_text(),names)", "'attempt-013.log').read_text(),names)")
s=s.replace('CLOSED: actual finite moment and every-natural-threshold tail; full mixing, asymptotics and novelty HOLD','PARTIAL: actual length/parameters and generic thinning/atom bound CLOSED; generic concentration and mixture OPEN')
(L/'certify.py').write_text(s)
print('immutable references verified; adapted certifier')
