import sys,runpy
from pathlib import Path
L=Path(__file__).resolve().parent
for id in ['1910.00846v1','2411.06468v1','2409.19768v1','2409.11285v1','2408.08935v1','2407.06321v1','2406.13888v1','2406.05777v1','2404.02236v1','2312.07591v1','2411.16284v1','2411.14661v1','2412.19338v1']:
 sys.argv=['work','fetch',id+'.pdf','https://arxiv.org/pdf/'+id];runpy.run_path(str(L/'work.py'),run_name='__main__')
