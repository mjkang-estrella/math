import pathlib,json,re
D=pathlib.Path(__file__).resolve().parents[1];x=json.loads((D/'extracted.json').read_text());p=D/'history-matches.txt';out={i:[] for i in x}
for line in p.open():
 for i,v in x.items():
  if re.search(r'(?<!\d)'+i+r'(?!\d)',line) or v['title'].lower() in line.lower():out[i].append(line[:2000].rstrip())
(D/'outputs/history-exact.json').write_text(json.dumps(out,indent=2));print({i:len(v) for i,v in out.items()})
