from itertools import permutations
from pathlib import Path
import json,resource,datetime
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(20,20))
P=list(permutations(range(5)))
squares={'cyclic': [[(h+i)%5 for i in range(5)] for h in range(5)], 'competitor':[[4,0,3,2,1],[3,2,4,1,0],[1,4,2,0,3],[2,1,0,3,4],[0,3,1,4,2]]}
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'permutations':120,'witnesses':{}}
for name,A in squares.items():
 classes=[[] for _ in range(5)]; assignments=[]
 for p in P:
  scores=[sum(x==y for x,y in zip(p,row)) for row in A]
  h=scores.index(max(scores));classes[h].append(p);assignments.append({'p':p,'agreement':scores,'h':h})
 # Independent definition via direct class scan for each (h,i,k), not agreement totals.
 M=[[[sum(p[i]==k for p in C) for k in range(5)] for i in range(5)] for C in classes]
 I=[[max(M[h][i][k] for i in range(5)) for k in range(5)] for h in range(5)]
 B=[[next(i for i in range(5) if M[h][i][k]==I[h][k]) for k in range(5)] for h in range(5)]
 win=[sum(p[B[h][k]]==k for h,C in enumerate(classes) for p in C) for k in range(5)]
 row_decoder_total=sum(sum(x==y for x,y in zip(p,A[h])) for h,C in enumerate(classes) for p in C)
 out['witnesses'][name]={'square':A,'latin':all(sorted(row)==list(range(5)) for row in A) and all(sorted(A[h][i] for h in range(5))==list(range(5)) for i in range(5)),'class_sizes':list(map(len,classes)),'magneticities_h_i_k':M,'intensities_h_k':I,'field':sum(map(sum,I)),'decoder_h_k':B,'wins_per_target':win,'row_decoder_total':row_decoder_total,'assignments':assignments}
assert out['witnesses']['cyclic']['field']==290
assert out['witnesses']['competitor']['field']==302
Path(__file__).with_name('enumeration-full.json').write_text(json.dumps(out,indent=2))
for n,d in out['witnesses'].items():print(n,{k:v for k,v in d.items() if k not in ['assignments','magneticities_h_i_k']})
