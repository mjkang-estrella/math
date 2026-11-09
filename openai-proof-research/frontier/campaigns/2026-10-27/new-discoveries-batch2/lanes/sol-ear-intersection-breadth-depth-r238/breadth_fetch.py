from retrieve import fetch
from concurrent.futures import ThreadPoolExecutor
items=[('boggle','1506.04173v1'),('divisibility','1611.07982v1'),('hill','1210.0835v1'),('ehrhart','1710.09507v1'),('hadamard','1307.4712v1'),('riordan','1707.06590v1'),('rectangular','1603.04476v1'),('twenty','1611.01655v1')]
with ThreadPoolExecutor(max_workers=3) as ex:list(ex.map(lambda x:fetch(x[0]+'.pdf','https://arxiv.org/pdf/'+x[1]),items))
