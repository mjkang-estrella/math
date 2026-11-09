import pathlib,json,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1];rs=json.loads((D/'extracted.json').read_text());pat=re.compile(r'(?<!\d)(?:'+ '|'.join(rs)+r')(?!\d)');out=[]
for line in (D/'history-matches.txt').read_text().splitlines():
 if len(line)<5000 and pat.search(line):out.append(line)
(D/'history-compact.txt').write_text('\n'.join(out)+'\n')
inv={}
for p in (D/'sources').glob('*.txt'):
 inv[p.name]=[{'line':i,'text':line} for i,line in enumerate(p.read_text().splitlines(),1) if re.search(r'\b(Example|Figure|Conjecture)\b',line)]
(D/'source-example-index.json').write_text(json.dumps(inv,indent=2))
