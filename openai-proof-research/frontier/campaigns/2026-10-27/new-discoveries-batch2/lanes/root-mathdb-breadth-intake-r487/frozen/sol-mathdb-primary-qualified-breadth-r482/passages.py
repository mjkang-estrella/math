import pathlib,json,hashlib,re
O=pathlib.Path(__file__).resolve().parent
refs=[{'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size} for p in sorted((O/'sources').glob('*'))]
(O/'source-bindings.json').write_text(json.dumps(refs,indent=2))
with (O/'primary-passages.txt').open('w') as out:
 for p in sorted((O/'sources').glob('*.txt')):
  ls=p.read_text().splitlines();hits=[i for i,l in enumerate(ls) if re.search(r'\bConjecture\s*[\dA-Z]|\bconjecture that|\bconjecture is|\bDefinition\s*\d',l)]
  ranges=set()
  for i in hits:
   ranges.update(range(max(0,i-3),min(len(ls),i+14)))
  out.write('\nSOURCE '+p.name+'\n')
  for i in sorted(ranges):out.write(f'{i+1}: {ls[i]}\n')
