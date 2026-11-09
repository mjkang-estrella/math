from fetch import get
import concurrent.futures
items=[('he-2021.pdf','https://www.engineering.uwaterloo.ca/~q7he/Z_PDF_PS_Published/2021_Reprint_JAP_SCV.pdf'),('nazarathy-catalogue.html','https://yoninazarathy.com/publications/'),('penaguiao-catalogue.html','https://raulpenaguiao.github.io/'),('1802.08400-abs.html','https://arxiv.org/abs/1802.08400')]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for v in ex.map(get,items):print(v,flush=True)
