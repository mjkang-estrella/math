from fetch import get
import concurrent.futures
items=[('omega-tree.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/40e572189e8b2852a6e9241e149bb27dab559dde?recursive=1')]
for a in ['2608.10629','2606.12197','1712.07867','1901.10911','1609.00320']:
 items.append((a+'.html','https://arxiv.org/html/'+a))
items += [('berge-sauer-tools.pdf','https://web.math.princeton.edu/~nalon/PDFS/tools1.pdf'),('bicrucial-journal.pdf','https://ecajournal.haifa.ac.il/Volume2022/ECA2022_S4PP4.pdf'),('1812.02761.pdf','https://arxiv.org/pdf/1812.02761')]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(get,items):print(r,flush=True)
