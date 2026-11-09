import pathlib,json
L=pathlib.Path.cwd();d=L/'downloads'
o=json.loads((d/'openalex-citing/body').read_text());print('CITING',json.dumps(o,indent=2))
t=json.loads((d/'pool-tree/body').read_text());print('CANDIDATES',*[x['path'] for x in t.get('tree',[]) if x['path'].startswith('candidates/')],sep='\n')
r=json.loads((L.parent/'expanded-corpus-r164/results.json').read_text())['333709'];(L/'mathdb-entry.json').write_text(json.dumps(r,indent=2));print('MATHDB',json.dumps(r,indent=2))
