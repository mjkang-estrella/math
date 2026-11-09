exec(open(__file__.replace('intake.py','freeze.py')).read().split('for d in')[0])
f=L/'bindings.json'; doc=json.loads(f.read_text()); refs=doc['refs']
R=B/'root-mathdb-breadth-intake-r403'; C=B/'pi-mathdb-full-corpus-inventory-r301'
def check(p,h,n):
 b=p.read_bytes(); assert len(b)==n and hashlib.sha256(b).hexdigest()==h,str(p);bind(p)
for e in json.loads((R/'manifest.json').read_text())['files']:check(R/e['path'],e['sha256'],e['size'])
for e in json.loads((R/'bindings.json').read_text()):check(Path(e['original']),e['sha256'],e['size'])
chunks=[e for e in json.loads((C/'manifest.json').read_text())['files'] if e['path'].startswith('corpus/')]
assert len(chunks)==20
for e in chunks:check(C/e['path'],e['sha256'],e['bytes'])
doc.update(refs=refs,phase='intake manifest and actual originals verified read-only; twenty chunks verified in place before content')
f.write_text(json.dumps(doc,indent=2)+'\n')
print('verified refs',len(refs),'chunks',len(chunks))
for n in ['coverage-delta.json','queue.json']:
 o=json.loads((R/n).read_text()); print(n,type(o).__name__, list(o)[:15] if isinstance(o,dict) else len(o))
