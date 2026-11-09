import pathlib,json,hashlib,re
D=pathlib.Path(__file__).resolve().parents[1]
# Snapshot all inspected ledger statuses without dumping private unrelated details.
for name,p in [('campaign',D.parent/'ledger.json'),('batch',D.parent.parent/'ledger.json')]:
 d=json.loads(p.read_text());(D/f'outputs/{name}-ledger-structure.json').write_text(json.dumps({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'top_level_keys':list(d) if isinstance(d,dict) else 'list','size':len(p.read_bytes())},indent=2))
# List every numbered example/figure in each downloaded primary version; exact bodies remain in sources.
lines=[]
for p in sorted((D/'sources').glob('*.txt')):
 if p.name=='atlas.txt':continue
 for n,line in enumerate(p.read_text().splitlines(),1):
  if re.search(r'^\s*(Figure|Example|Remark|Conjecture)\s+[0-9]',line):lines.append({'path':str(p.relative_to(D)),'line':n,'text':line})
(D/'outputs/printed-examples.json').write_text(json.dumps(lines,indent=2))
