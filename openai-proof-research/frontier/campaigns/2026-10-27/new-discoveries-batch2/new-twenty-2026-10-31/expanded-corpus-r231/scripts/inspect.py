import pathlib,json,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
out=[]
for p in sorted((D/'sources').glob('*.txt')):
 lines=p.read_text().splitlines();matches=[]
 for i,l in enumerate(lines):
  if re.search(r'Conjecture|^Definition|^Example|Figure',l):matches.append({'line':i+1,'context':'\n'.join(lines[max(0,i-1):i+8])})
 out.append({'file':p.name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'passages':matches})
(D/'source-passages.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
o=json.loads((D/'sources/Sq-head.json').read_text());sha=o['sha'];todo=[('Sq-README.md','https://raw.githubusercontent.com/ShengtongZhang-alt/Sq/'+sha+'/README.md')]
(D/'fetch-sq.json').write_text(json.dumps(todo)+'\n')
print('source passage catalogue',len(out),'text files; Sq head',sha)
