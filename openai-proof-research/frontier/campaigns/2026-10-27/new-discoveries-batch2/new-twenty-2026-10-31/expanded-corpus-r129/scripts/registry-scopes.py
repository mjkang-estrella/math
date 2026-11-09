import pathlib,json,sys,re
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'scripts'))
from fetch import get
h=json.loads((D/'sources/omega-head.json').read_text())['sha'];repo='the-omega-institute/trureturing'
print(get(('omega-root.json',f'https://api.github.com/repos/{repo}/git/trees/{h}')),flush=True)
root=json.loads((D/'sources/omega-root.json').read_text())
for x in root['tree']:
 if x['path'] in ['D5','Problems']:
  print(get((f'omega-{x["path"]}.json',f'https://api.github.com/repos/{repo}/git/trees/{x["sha"]}?recursive=1')),flush=True)
# immutable proof bodies of promising path hits
paths=['D5/S1/Words/Patterns/Separable/RecordPeak.lean','D5/S1/Words/Patterns/Separable/RecordFirstDecline.lean','D5/S1/Words/Patterns/Separable/RecordNewtonPositivity.lean']
for p in paths:print(get((p.rsplit('/',1)[-1],f'https://raw.githubusercontent.com/{repo}/{h}/{p}')),flush=True)
for p in (D/'sources').glob('omega-*.json'):
 try:o=json.loads(p.read_text())
 except:continue
 hits=[x['path'] for x in o.get('tree',[]) if re.search('erdos.deep|separable|steiner|hilton.milner|renewal|neural.ideal|hawkes|tournament|discus|descendent|censored|hypergeometric|pseudocircle|gamma',x['path'],re.I)]
 (D/f'outputs/{p.stem}-matches.txt').write_text('\n'.join(hits))
