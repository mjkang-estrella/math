import pathlib,re,json
D=pathlib.Path(__file__).resolve().parents[1];out={}
for p in sorted((D/'sources').glob('pdf-*/text.txt')):
 a=p.parent.name[4:];ls=p.read_text().splitlines();snips=[]
 for i,s in enumerate(ls):
  if re.search(r'Conjecture [\d]|Conjecture\.|conjecture was|conjecture is|conjecture.*proved|conjecture.*disprov|conjecture.*solved',s):
   snips.append({'line':i+1,'text':'\n'.join(ls[max(0,i-2):i+10])})
 out[a]=snips
(D/'outputs/source-excerpts.json').write_text(json.dumps(out,indent=2));
for a,snips in out.items():
 print('\n',a)
 for x in snips[:3]:print(x['text'][:800])
