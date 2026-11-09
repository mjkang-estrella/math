"""Read-only frozen-input review checks. Writes only this review's log via caller."""
from pathlib import Path
from itertools import permutations,combinations,product
from collections import defaultdict
from fractions import Fraction as Q
import json,re,ast,hashlib
p=Path(__file__).parent;b=p.parent;old=b/'hereditary-trace-fresh-r1';r2=b/'trace-deformation-r2'
def canon(w):return min(w[k:]+w[:k] for k in range(len(w)))
def fundamental(bs):
 out=defaultdict(Q)
 for perm in permutations(range(4)):
  unseen=set(range(4));ws=[]
  while unseen:
   j=min(unseen);w=()
   while j in unseen:
    unseen.remove(j);w+=bs[j];j=perm[j]
   ws.append(canon(w))
  out[tuple(sorted(ws))]+=(-1)**(4-len(ws))
 return {m:c for m,c in out.items() if c}
def parse(xs):return {tuple(tuple(map(int,w)) for w in x['traces']):Q(x['coefficient']) for x in xs}
def signature(pol):return tuple(sorted(pol.items()))
d=json.loads((old/'trace-exact-polynomials.json').read_text())
def degree(w):return tuple(w.count(a) for a in (1,2,3))
def sub(a,bb):return tuple(x-y for x,y in zip(a,bb))
def necklaces(dd):
 return sorted({canon(w) for w in set(permutations(tuple(a for a,n in zip((1,2,3),dd) for _ in range(n))))}) if sum(dd) else []
def monomials(dd,lo=()):
 if not sum(dd):return [()]
 ans=[]
 for ee in product(*(range(n+1) for n in dd)):
  if not sum(ee):continue
  for w in necklaces(ee):
   if w>=lo:ans.extend((w,)+m for m in monomials(sub(dd,ee),w))
 return ans
witnesses={};count=0
for dd in product(range(4),range(3),range(3)):
 if not 4<=sum(dd)<=6:continue
 tuples=set()
 for w in set(permutations(tuple(a for a,n in zip((1,2,3),dd) for _ in range(n)))):
  for cuts in combinations(range(1,len(w)),3):
   t=(0,)+cuts+(len(w),);tuples.add(tuple(sorted(w[t[i]:t[i+1]] for i in range(4))))
 for bs in sorted(tuples):
  f=fundamental(bs)
  for m in monomials(sub((3,2,2),dd)):
   pol={tuple(sorted(m+k)):c for k,c in f.items()};count+=1
   witnesses[signature(pol)]=(bs,m)
assert all(signature(parse(col)) in witnesses for col in d['lower_identity_products'])
# Check the saved 713 entries are exactly the entries extracted from the primary thesis.
th=(old/'sources/hoge-thesis.txt').read_text();seg=th[th.index('[[1, 2, 3], [4, 5], [6], [7]]   3055/864'):th.index('Dabei steht zum Beispiel')]
rows=re.findall(r'(\[\[(?:[0-9,\[\] ]+)\]\])\s*([−-]?\d+/\d+)',seg)
actual=[(tuple(tuple(a) for a in ast.literal_eval(bs)),Q(c.replace('−','-'))) for bs,c in rows]
ex=json.loads((r2/'explicit-reduction.json').read_text());saved=[(tuple(tuple(map(int,w)) for w in a['blocks']),Q(a['coefficient'])) for a in ex['fundamental_combination']]
assert actual==saved and len(actual)==713
# Audit every literal table tuple's actual length; ignore printed degree headings.
s=(old/'sources/trace.txt').read_text();table=s[s.index('Theorem 4.1.'):s.index('Remark 4.2.')]
tuples=[tuple(m) for m in re.findall(r'\((\d+),\s*(\d+),\s*(\d+),\s*(\d+)\)',table)]
assert tuples and [bs for bs in tuples if sum(map(len,bs))<=7]==[('111','22','3','3')]
assert all(sum(map(len,bs))>=8 for bs in tuples if bs!=('111','22','3','3'))
# Canonical top words for all six source letter permutations; two can have target weight.
tops=[]
for perm in permutations((1,2,3)):
 bs=tuple(tuple(perm[a-1] for a in w) for w in ((1,1,1),(2,2),(3,),(3,)))
 if tuple(sum(w.count(a) for w in bs) for a in (1,2,3))==(3,2,2):
  tops.append({'perm':perm,'top':[(m,str(c)) for m,c in fundamental(bs).items() if len(m)==1]})
assert len(tops)==2
print(json.dumps({'status':'PASS','lower_columns_verified_as_actual_identity_products':len(d['lower_identity_products']),'enumerated_products':count,'thesis_entries_match_primary_text':713,'literal_table_tuples':len(tuples),'only_degree7_tuple':['111','22','3','3'],'stabilizer_top_checks':tops,'Lean_checked':False},indent=2))
