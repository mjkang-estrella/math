import pathlib,json,re
D=pathlib.Path(__file__).resolve().parents[1]
x=json.loads((D/'extracted.json').read_text())
pat=re.compile(r'(?<![a-zA-Z0-9])(?:'+'|'.join(x)+r')(?![a-zA-Z0-9])')
rows=[]
for line in (D/'history-matches.txt').read_text().splitlines():
 p=line.split(':',2)
 if len(p)<3: continue
 path,num,body=p
 if '/corpus/' in path or '/sources/' in path or 'registry' in pathlib.Path(path).name: continue
 if pat.search(body) or any(o['title'].lower() in body.lower() for o in x.values()): rows.append(line)
(D/'outputs/history-filtered.txt').write_text('\n'.join(rows)+'\n')
