from fetch import get
import concurrent.futures
ids=['2204.07219','2608.12266','1802.08400v1','2102.09405','1212.3726']
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for v in ex.map(get,[(i+'.pdf','https://arxiv.org/pdf/'+i) for i in ids]):print(v,flush=True)
