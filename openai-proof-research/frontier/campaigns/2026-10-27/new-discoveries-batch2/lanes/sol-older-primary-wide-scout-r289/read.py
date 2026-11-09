import pathlib,hashlib,json,re
L=pathlib.Path(__file__).resolve().parent
out={}
for p in sorted((L/'texts').glob('*.txt')):
 a=hashlib.sha256(p.read_bytes()).hexdigest();lines=p.read_text().splitlines();selected=set()
 for i,s in enumerate(lines):
  if re.match(r'^\s*(Conjecture|CONJECTURE|Problem|Theorem 1\.|Theorem 2\.)',s):selected.update(range(max(0,i-2),min(len(lines),i+21)))
 out[p.name]={'sha256':a,'passages':[[i+1,lines[i]] for i in sorted(selected)]}
 print('\n###',p.name);print('\n'.join(f'{i+1}: {lines[i]}' for i in sorted(selected)))
 assert a==hashlib.sha256(p.read_bytes()).hexdigest()
(L/'read-passages.json').write_text(json.dumps(out,indent=2))
