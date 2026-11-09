from fetch import get
for a in ['1402.5452','1404.2743','1612.03325']:
 print(get((a+'.pdf','https://arxiv.org/pdf/'+a)),flush=True)
