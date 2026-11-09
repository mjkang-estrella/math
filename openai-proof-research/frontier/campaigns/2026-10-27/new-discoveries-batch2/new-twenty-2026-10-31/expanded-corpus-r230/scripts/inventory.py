import pathlib,json,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1];x=json.loads((D/'extracted.json').read_text());out={}
for p in sorted((D/'sources').glob('*.txt')):
 if any(t in p.name for t in ['2306.12543','2306.14389','2307.04687','2308.16553','2309.00757']):
  ls=p.read_text().splitlines();out[p.name]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'printed_example_figure_mentions':[{'line':j+1,'text':s.strip()} for j,s in enumerate(ls) if re.search(r'\b(?:Example|Figure|Fig\.)\s*\d',s)]}
(D/'printed-example-inventory.json').write_text(json.dumps(out,indent=2)+'\n')
# Short, bounded history snippets avoid unrelated giant numeric rows.
ls=(D/'history-matches.txt').read_text().splitlines();(D/'history-summary.txt').write_text('\n'.join(s[:400] for s in ls)+'\n')
