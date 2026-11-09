import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,runpy,sys
L=pathlib.Path(__file__).resolve().parent
rows=json.loads((L/'reservation.json').read_text())['rows'];sys.argv=['fetch.py',json.dumps([[str(r['mathdb_id'])+'.html',r['source_url']] for r in rows])];runpy.run_path(str(L/'fetch.py'),run_name='__main__')
