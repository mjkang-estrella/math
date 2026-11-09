import pathlib,json,hashlib
from fractions import Fraction as F
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'manifest.json').read_text());assert 'manifest.json' not in m and 'verification-receipt.json' not in m
for p,h in m.items():assert sha(L/p)==h,p
scientific=[]
for s in (L/'bindings.jsonl').read_text().splitlines():
 r=json.loads(s)
 if r['category']!='administrative':
  assert sha(pathlib.Path(r['original']))==sha(L/r['copy'])==r['sha256'];scientific.append(r['copy'])
for r in json.loads((L/'primarybindings.json').read_text()):assert sha(L/r['file'])==r['sha256']
for s in (L/'derivations.jsonl').read_text().splitlines():
 r=json.loads(s);assert sha(L/r['source'])==r['sha256'];assert sha(L/r['text'])==r['text_sha256']
c=json.loads((L/'checks.json').read_text());A=c['abstract_action_obstruction']['A'];v=list(map(F,c['abstract_action_obstruction']['zero_sum_vector']));assert sum(v)==0
N=12
s=[i^1 for i in range(N)];t=[11 if i==0 else 0 if i==11 else ((i-1)^1)+1 for i in range(N)]
for i in range(N):
 assert s[s[i]]==t[t[i]]==i
 x=i
 for k in range(6):x=t[s[x]]
 assert x==i
 for j in range(N):assert A[i][j]==3*(i==j)+2*(s[i]==j)+2*(t[i]==j)+(s[t[i]]==j)+(t[s[i]]==j)
num=sum(v[i]*A[i][j]*v[j] for i in range(N) for j in range(N));den=sum(x*x for x in v)
assert (num,den)==(70,10) and num>4*den
assert sum(r['nonchain_checked'] for r in c['poset_checks'])==206
receipt={'status':'PASS','manifest_sha256':sha(L/'manifest.json'),'manifest_files':len(m),'scientific_local_originals_and_copies_verified':scientific,'remote_body_and_derived_text_hashes':'PASS','abstract_obstruction_independent_matrix_formula':'PASS, Rayleigh 7 > 4','administrative':'snapshots only; not compared to mutable live ledger','mathematical_scope':'Verification is packet integrity and bounded controls, not a full proof or novelty certificate.','counts_unchanged':[9,39,40]}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
