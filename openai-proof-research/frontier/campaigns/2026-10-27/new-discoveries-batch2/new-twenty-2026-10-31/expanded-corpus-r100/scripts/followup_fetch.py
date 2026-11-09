from fetch import get
for a in ['2506.23936','2607.16810']:print(get((a+'.html','https://arxiv.org/html/'+a)),flush=True)
