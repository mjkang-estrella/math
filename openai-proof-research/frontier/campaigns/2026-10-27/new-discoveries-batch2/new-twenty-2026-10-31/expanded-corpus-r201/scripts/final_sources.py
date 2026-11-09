import pathlib,json,sys,re,subprocess
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import fetch,D
reg=json.loads((D/'outputs/registry-screen.json').read_text());out=[]
# Reuse complete pinned preprint catalogue only because live HEAD is unchanged.
cat=D.parents[5]/'sources/preprints-tree.json'
base=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/preprints-tree.json')
if base.exists():
 t=json.loads(base.read_text());paths=[x['path'] for x in t.get('tree',[])]
 print('preprint matches',*[p for p in paths if re.search('boone|panyushev|symplectic.*content|bruhat.*automorph|quadrangulation|hard.squares',p,re.I)],sep='\n')
urls=[('boone','https://raw.githubusercontent.com/openai/math/'+reg['heads']['openai/math']+'/preprints/Finite-algebraic-envelopes-and-the-Boone-Higman-conjecture-September-23-2026/paper.pdf'),('bruhat-publisher','https://doi.org/10.1007/s00209-022-03194-2'),('bruhat-proceedings','https://www.mat.univie.ac.at/~slc/wpapers/FPSAC2023/11.pdf'),('chern-author','https://shanechern.github.io/publications/preprints/079.%20Asymmetric%20Rogers-Ramanujan%20type%20identities.pdf'),('tutaj-published','https://sciendo.com/2/v2/download/article/10.2478/aupcsm-2018-0010.pdf')]
for label,u in urls:
 r=fetch(u,label);out.append(r)
 if r.get('status')==200 and pathlib.Path(r['body']).read_bytes().startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',r['body'],str(D/f'outputs/{label}.txt')])
# Definitions needed to compare the public Lean endpoint to the source counting conjecture.
sha=reg['heads']['the-omega-institute/trureturing']
out.append(fetch(f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{sha}/D5/S3/Combinatorics/PopStack/PopStackDefs.lean','popstack-defs'))
(D/'outputs/final-source-receipts.json').write_text(json.dumps(out,indent=2));print([(x['url'],x.get('status')) for x in out])
