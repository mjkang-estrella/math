from pathlib import Path
import json,itertools
L=Path(__file__).resolve().parents[1]
exec((L/'scripts/qsearch.py').read_text().split('rng=random.Random(237)')[0])
S=spaces(4);candidate=json.loads((L/'outputs/q-nondegenerate-candidate.json').read_text());r={frozenset(x['space']):x['rank'] for x in candidate['ranks']}
p=91 # x^6+x^4+x^3+x+1 from Example 21
alpha=2;alpha8=1
for i in range(8):alpha8=mul(alpha8,alpha,p)
G=[[1,alpha,0,0],[0,0,1,alpha8]]
im={v:tuple(__import__('functools').reduce(int.__xor__,(G[i][j] for j in range(4) if v>>j&1),0) for i in range(2)) for v in range(16)}
sr={a:rank([im[v] for v in a],p) for a in S}
for basis in itertools.permutations(range(1,16),4):
 images=[0]*16
 for v in range(1,16):images[v]=__import__('functools').reduce(int.__xor__,(basis[i] for i in range(4) if v>>i&1),0)
 if len(set(images))!=16:continue
 if all(r[a]==sr[frozenset(images[v] for v in a)] for a in S):
  out={'source':'arXiv:2109.13637 v4 Example 21 second displayed matrix','source_modulus':p,'source_matrix':G,'candidate_matrix':candidate['G'],'linear_map_basis_images':basis,'subspaces_compared':len(S),'all_ranks_equal':True};print(out);(L/'outputs/q-source-isomorphism.json').write_text(json.dumps(out,indent=2));break
else:print('no isomorphism')
