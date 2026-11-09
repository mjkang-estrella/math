import pathlib,json,re
D=pathlib.Path(__file__).resolve().parents[1];x=json.loads((D/'extracted.json').read_text());out={}
for i,o in x.items():
 pat=re.compile(r'(?<!\d)'+i+r'(?!\d)|'+re.escape(o['title']),re.I);hits=[]
 for line in (D/'history-matches.txt').read_text().splitlines():
  m=pat.search(line)
  if m:hits.append({'file_line':line[:line.find(':',line.find(':')+1)] if ':' in line else '', 'context':line[max(0,m.start()-100):m.end()+500]})
 out[i]=hits
(D/'history-screen.json').write_text(json.dumps(out,indent=2));print({k:len(v) for k,v in out.items()})
