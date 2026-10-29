exec((__import__('pathlib').Path(__file__).parent/'read.py').read_text().split("get('sahbi.raw'")[0])
import datetime,re
h=json.loads((L/'sources/omega-HEAD.json').read_bytes());head=h['sha']
b=get('omega-delta.json',f'https://api.github.com/repos/the-omega-institute/trureturing/compare/73a5033dd654a16a14fcd1b13277f1a03d81d826...{head}')
paths=['Problems/blitvic-kammoun-steingrimsson-2026-packing-maximum.md','Library/PermutationPatterns/blitvickammounsteingrimsson2026patterns.md','Problems/sahbi-2026-star-forming-bipartite-refutation.md']
if b:
 d=json.loads(b);print('DELTA',d.get('total_commits'),[(f['filename'],f['status']) for f in d.get('files',[])])
 for f in d.get('files',[]):
  if f['status']!='removed' and re.search('pattern|pack|blit|sahbi|separat|cutoff',f['filename'],re.I):paths.append(f['filename'])
for i,p in enumerate(paths):get(f'literal-{i}.txt',f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{head}/{p}')
get('precursor.pdf','https://www.mat.univie.ac.at/~slc/wpapers/FPSAC2023/61.pdf')
get('covers-abs.raw','https://arxiv.org/abs/2610.29846')
get('sahbi-v4.raw','https://arxiv.org/html/2610.03785v4')
(L/'refresh-http.json').write_text(json.dumps(records,indent=2))
# Save only exact local candidate-related body hits, not manifest path matches.
R=L.parents[6] if False else __import__('pathlib').Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
pat=re.compile(rb'2610.29846|blitvic|pattern.cover|cutoff.{0,80}pattern|uniform.{0,80}representative',re.I)
with (L/'duplicate-relevant.jsonl').open('w') as out:
 for row in map(json.loads,(L/'duplicate-hits.jsonl').open()):
  p=R/row['path']
  if p.suffix not in ['.md','.lean','.tex','.py'] or p.stat().st_size>2000000:continue
  b=p.read_bytes()
  if pat.search(b):out.write(json.dumps({'path':row['path'],'sha256':row['sha256'],'text':b.decode(errors='replace')})+'\n')
