from fetch import get
for a in ['1612.03332','1312.7555v1']:
 print(get((a+'.pdf','https://arxiv.org/pdf/'+a)),flush=True)
