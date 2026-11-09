import pathlib,json,re
D=pathlib.Path(__file__).resolve().parents[1];out={}
for row in json.loads((D/'reservation.json').read_text())['rows']:
 i=str(row['mathdb_id']);paths=sorted((D/'sources').glob(i+'-v*-pdf-*/text.txt'))
 snippets=[]
 for p in paths:
  lines=p.read_text().splitlines();matches=[j for j,l in enumerate(lines) if re.search(r'(Conjecture\s+[\dA-Z]|We conjecture|we conjecture)',l)]
  for j in matches:snippets.append({'path':str(p),'line':j+1,'text':'\n'.join(lines[max(0,j-2):j+20])})
 out[i]=snippets
(D/'outputs/source-excerpts.json').write_text(json.dumps(out,indent=2))
for i in ['362401','363679','358199','354443','356013','356197','356992']:
 print('\nID',i)
 for x in out[i][-3:]:print(x['path'],x['line'],x['text'])
