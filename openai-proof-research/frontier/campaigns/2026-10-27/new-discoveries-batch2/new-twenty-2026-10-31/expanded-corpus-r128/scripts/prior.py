import pathlib,json,importlib.util
D=pathlib.Path(__file__).resolve().parents[1];s=importlib.util.spec_from_file_location('f',D/'scripts/fetch.py');f=importlib.util.module_from_spec(s);s.loader.exec_module(f)
print(f.get(('maxout-prior-head.json','https://api.github.com/repos/reuellee/finite-certificates/commits/HEAD')))
p=D/'sources/maxout-prior-head.json'
if p.exists():
 sha=json.loads(p.read_text())['sha']
 for path in ['README.md','ai/maxout/capstone/CAPSTONE.md','ai/maxout/paper/main.tex']:
  print(f.get(('maxout-prior-'+path.split('/')[-1],'https://raw.githubusercontent.com/reuellee/finite-certificates/'+sha+'/'+path)))
print(f.get(('continued-journal.pdf','https://math.colgate.edu/~integers/z89/z89.pdf')))
