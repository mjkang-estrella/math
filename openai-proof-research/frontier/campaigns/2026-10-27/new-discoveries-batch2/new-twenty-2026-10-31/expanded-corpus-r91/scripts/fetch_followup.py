from fetch import get
for a in ['2610.21636','2606.12380','2606.22697']:
 print(get((a+'.html','https://arxiv.org/html/'+a)),flush=True)
print(get(('2601.16039.pdf','https://arxiv.org/pdf/2601.16039')),flush=True)
