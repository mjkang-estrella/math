import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parents[1];out={}
for p in sorted((L/'logs').glob('*.txt')):
 records=[];nonjson=[]
 for line in p.read_text(errors='replace').splitlines():
  try:records.append(json.loads(line))
  except ValueError:nonjson.append(line)
 out[p.name]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'records':records,'other_output':nonjson}
(L/'outputs/search-coverage.json').write_text(json.dumps(out,indent=2))
print('coverage logs',len(out))
