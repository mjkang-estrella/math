from fetch import get
import concurrent.futures
items=[('omega-changes.json','https://api.github.com/repos/the-omega-institute/trureturing/compare/790d20daa36ba56dd2bd55777592ac36cf8a92ef...8d9d5d9ee811f5c54fdd5ef5f2e1c59bf2b32d95'),('2608.25746.html','https://arxiv.org/html/2608.25746'),('2604.08013.html','https://arxiv.org/html/2604.08013'),('direction-prior.html','https://chinaxiv.org/abs/202610.00057'),('catalan-prior.json','https://api.github.com/repos/creelie/Paper_3/commits/HEAD'),('2607.28784.pdf','https://arxiv.org/pdf/2607.28784'),('2607.28653v1.html','https://arxiv.org/html/2607.28653v1')]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for v in ex.map(get,items):print(v,flush=True)
