"""Independent transparent exhaustive certificate over all 120 permutations."""
from pathlib import Path
from itertools import permutations
from collections import Counter
import json,csv
L=Path(__file__).resolve().parent
A=[[ (h+i)%5 for i in range(5)] for h in range(5)]
B=[[4,0,3,2,1],[3,2,4,1,0],[1,4,2,0,3],[2,1,0,3,4],[0,3,1,4,2]]
P=list(permutations(range(5)));assert len(P)==len(set(P))==120
out={}
for name,S in [('cyclic',A),('competitor',B)]:
 assert all(sorted(row)==list(range(5)) for row in S)
 assert all(sorted(S[h][i] for h in range(5))==list(range(5)) for i in range(5))
 records=[];M=[[[0]*5 for i in range(5)] for h in range(5)]
 for p in P:
  scores=[sum(p[i]==row[i] for i in range(5)) for row in S];h=scores.index(max(scores))
  records.append({'permutation':p,'agreements':scores,'message':h})
  for i,k in enumerate(p):M[h][i][k]+=1
 I=[[max(M[h][i][k] for i in range(5)) for k in range(5)] for h in range(5)]
 decoder=[[next(i for i in range(5) if S[h][i]==k) for k in range(5)] for h in range(5)]
 assert all(M[h][decoder[h][k]][k]==I[h][k] for h in range(5) for k in range(5))
 out[name]={'square':S,'fibre_sizes':[sum(r['message']==h for r in records) for h in range(5)],'magneticities_h_i_k':M,'intensities_h_k':I,'inverse_row_decoder_h_k':decoder,'field':sum(map(sum,I)),'target_counts':[sum(I[h][k] for h in range(5)) for k in range(5)],'maximum_agreement_histogram':dict(sorted(Counter(max(r['agreements']) for r in records).items())),'permutations':records}
assert out['cyclic']['field']==290 and out['competitor']['field']==302
(L/'certificate.json').write_text(json.dumps(out,indent=2)+'\n')
with (L/'partition.csv').open('w') as f:
 w=csv.writer(f);w.writerow(['permutation','cyclic_message','competitor_message','cyclic_scores','competitor_scores'])
 for a,b in zip(out['cyclic']['permutations'],out['competitor']['permutations']):w.writerow([''.join(map(str,a['permutation'])),a['message'],b['message'],','.join(map(str,a['agreements'])),','.join(map(str,b['agreements']))])
print(json.dumps({k:{x:v[x] for x in ['fibre_sizes','intensities_h_k','field','target_counts','maximum_agreement_histogram']} for k,v in out.items()},indent=2))
