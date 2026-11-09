#!/usr/bin/env python3
"""Direct, isolated CLI replays. No generator/checker imports or monkeypatches."""
import argparse
import collections
import concurrent.futures
import hashlib
import json
import pathlib
import subprocess
import sys
import time
sys.dont_write_bytecode=True
HERE=pathlib.Path(__file__).resolve().parent


def worker(path):
    before=hashlib.sha256(path.read_bytes()).hexdigest()
    start=time.monotonic()
    command=['bash','-c','ulimit -v 8000000; python3 -I "$@"','nd-sym-check',
             str(HERE/'check_sym.py'),str(path),'10']
    try:
        p=subprocess.run(command,capture_output=True,text=True,timeout=600)
        parsed=json.loads(p.stdout.strip().splitlines()[-1])
        if p.returncode or parsed['result']!='PASS':
            raise ValueError((p.returncode,parsed,p.stderr[-1000:]))
        after=hashlib.sha256(path.read_bytes()).hexdigest()
        assert before==after,'certificate changed while checking'
        return {'label':'PROVED','result':'PASS','sha256':after,'check':parsed,
                'seconds':round(time.monotonic()-start,3),'command':command}
    except Exception as e:
        return {'label':'COMPUTED','result':'FAIL','error':repr(e),
                'seconds':round(time.monotonic()-start,3),'command':command}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--workers',type=int,default=12)
    args=ap.parse_args()
    assert 1<=args.workers<=12
    paths=sorted(set(list((HERE/'crosscheck').rglob('*.jsonl'))+
                     list((HERE/'certs').rglob('*.jsonl'))+
                     list((HERE/'controls').glob('*.jsonl'))+
                     list(HERE.glob('smoke.jsonl'))+list(HERE.glob('probe*.jsonl'))))
    output=HERE/'standalone_checks.json'
    results={}
    print('files',len(paths),flush=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        jobs={pool.submit(worker,p):str(p.relative_to(HERE)) for p in paths}
        for future in concurrent.futures.as_completed(jobs):
            key=jobs[future];results[key]=future.result()
            if len(results)%25==0 or len(results)==len(paths) or results[key]['result']!='PASS':
                tmp=output.with_suffix('.json.tmp')
                tmp.write_text(json.dumps({'label':'COMPUTED','checker_sha256':hashlib.sha256((HERE/'check_sym.py').read_bytes()).hexdigest(),
                                'brute_Lmax':10,'files':results},indent=1)+'\n')
                tmp.replace(output)
            if len(results)%100==0 or results[key]['result']!='PASS':
                print(len(results),'/',len(paths),key,results[key]['result'],flush=True)
    print('counts',dict(collections.Counter(x['result'] for x in results.values())),flush=True)

if __name__=='__main__':main()
