from fetch import get
for a in ['2505.05339','2506.21286']:
 print(get((a+'.pdf','https://arxiv.org/pdf/'+a)),flush=True)
