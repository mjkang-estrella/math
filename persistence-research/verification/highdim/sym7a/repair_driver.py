import sys
sys.dont_write_bytecode=True
import pathlib
h=pathlib.Path(__file__).resolve().parent
p=h/'run7a.py';s=p.read_text().replace('import argparse,collections,concurrent.futures,hashlib,json,pathlib,signal,time','import argparse,collections,concurrent.futures,hashlib,json,pathlib,signal,time,multiprocessing,os')
s=s.replace("g.run(schedule);g.write(fn,extra={'stage':stage,'configuration':name,'peeling':True})", "g.run(schedule)\n    pending=fn.with_suffix('.pending.'+str(os.getpid()))\n    g.write(pending,extra={'stage':stage,'configuration':name,'peeling':True})\n    try:os.link(pending,fn)\n    except FileExistsError:pass\n    pending.unlink()")
s=s.replace('ProcessPoolExecutor(max_workers=a.workers)',"ProcessPoolExecutor(max_workers=a.workers,mp_context=multiprocessing.get_context('fork'))")
p.write_text(s)
p=h/'replay7a.py';s=p.read_text().replace("records.get(f,{}).get(w,{}).get('result')!='PASS'", "not (records.get(f,{}).get(w,{}).get('result')=='PASS' and records[f][w]['sha256']==sha(f) and records[f][w]['checker_sha256']==sha(H.parent/'sym5/check_sym5.py' if w=='M' else R/'verification/indep5/check_sym_F5.py'))")
p.write_text(s)
