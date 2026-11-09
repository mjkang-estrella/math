import pathlib,json,importlib.util,itertools
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r174')
s=importlib.util.spec_from_file_location('seq',L/'scripts/sequence_search.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
def brute(w,u):
 r=max(u)+1
 for perm in itertools.permutations(range(3),r):
  v=[perm[x] for x in u];j=0
  for a in w:
   if a==v[j]:
    j+=1
    if j==len(v):return True
 return False
patterns=[(0,0),(0,1,0),(0,0,1,1),(0,1,2),(0,1,0,2,1),(0,1,2,0,2,1,2)]
checks=0
for n in range(1,7):
 for w in itertools.product(range(3),repeat=n):
  for u in patterns:
   assert m.contains(w,u)==brute(w,u),(w,u)
   checks+=1
# Independently check saved terminal words for source-rule saturation.
saturated=0
for line in (L/'outputs/sequence-search.jsonl').read_text().splitlines():
 d=json.loads(line);w=d['final_word'];u=tuple(ord(x)-97 for x in d['pattern']);r=max(u)+1
 assert not m.contains(w,u)
 assert all(len(set(w[j:j+r]))==r for j in range(len(w)-r+1))
 for x in range(d['through_n']):
  for p in range(len(w)+1):
   z=w[:p]+[x]+w[p:]
   sparse=all(len(set(z[j:j+r]))==r for j in range(len(z)-r+1))
   assert not sparse or m.contains(z,u)
 saturated+=1
out=dict(independent_subsequence_comparisons=checks,terminal_words_independently_checked_for_sparsity_avoidance_and_saturation=saturated,failures=0)
(L/'outputs/search-validation.json').write_text(json.dumps(out,indent=2));print(out)
