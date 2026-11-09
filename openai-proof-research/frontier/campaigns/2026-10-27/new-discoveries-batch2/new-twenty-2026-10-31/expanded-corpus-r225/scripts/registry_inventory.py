import pathlib,json,re,importlib.util,hashlib
D=pathlib.Path(__file__).resolve().parents[1];s=importlib.util.spec_from_file_location('f',D/'scripts/fetch.py');f=importlib.util.module_from_spec(s);s.loader.exec_module(f)
sha=json.loads((D/'sources/openai-head.json').read_text())['sha'];print(f.get('openai-root.json',f'https://api.github.com/repos/openai/math/git/trees/{sha}'),flush=True)
p=D/'sources/openai-root.json'
if p.exists():
 for e in json.loads(p.read_text()).get('tree',[]):
  if e['path']=='preprints':print(f.get('openai-preprints.json',f'https://api.github.com/repos/openai/math/git/trees/{e["sha"]}?recursive=1'),flush=True)
  if e['path']=='overview.tex':print(f.get('openai-overview.tex',f'https://raw.githubusercontent.com/openai/math/{sha}/overview.tex'),flush=True)
# inventories preserve all example/figure captions for versioned source review; no claim graphical contents were visually inspected
out={}
for p in sorted((D/'sources').glob('*.txt')):
 if re.match(r'\d{4}\.\d+(v\d+)?\.txt',p.name):
  ls=p.read_text().splitlines();out[p.name]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'examples_figures': [{'line':i+1,'text':' '.join(ls[i:i+4])[:2500]} for i,l in enumerate(ls) if re.match(r'Figure\s+\d|Example\s+\d',l)]}
(D/'source-example-inventory.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
