#!/usr/bin/env python3
"""Fresh review HTTP responses; execution is not part of offline verification."""
from pathlib import Path
import concurrent.futures
import datetime
import hashlib
import json
import subprocess
import urllib.request
import urllib.error

ROOT = Path(__file__).resolve().parents[3]
S = ROOT/'frontier/sources/i38_propeller_stability_r2'
L = S/'literature'
REQUESTS = [
 ('hjn-author.pdf','https://web.math.princeton.edu/~naor/homepage%20files/PropR3.pdf'),
 ('hjn-current.html','https://arxiv.org/abs/1112.2993'),
 ('hjn-v2.pdf','https://arxiv.org/pdf/1112.2993v2'),
 ('kn-author.pdf','https://web.math.princeton.edu/~naor/homepage%20files/kernel.pdf'),
 ('hei14-author.pdf','https://www.stevenheilman.org/~heilman/papers/SSC.pdf'),
 ('corthree-current.html','https://arxiv.org/abs/2306.03312'),
 ('corthree-v3.pdf','https://arxiv.org/pdf/2306.03312v3'),
]
def fetch(item):
    name,url=item
    row={'name':name,'request':{'method':'GET','url':url},
         'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        try:
            response=urllib.request.urlopen(url,timeout=50)
        except urllib.error.HTTPError as ex:
            response=ex
        with response as f:
            data=f.read();row.update(status=f.status,headers=dict(f.headers),final_url=f.url)
        (L/name).write_bytes(data)
        row.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),pdf=data.startswith(b'%PDF'))
        if row['pdf']:
            proc=subprocess.run(['pdftotext','-layout',str(L/name),str((L/name).with_suffix('.txt'))],capture_output=True)
            row['pdftotext_returncode']=proc.returncode
        old=ROOT/'frontier/sources/i38_inequality_stability_discovery/literature'/name
        row['equal_to_author_response']=old.exists() and old.read_bytes()==data
    except Exception as ex:
        row['error']=repr(ex)
    return row

if __name__=='__main__':
    L.mkdir(parents=True,exist_ok=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        rows=list(pool.map(fetch,REQUESTS))
    (L/'manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
    print(json.dumps([{k:v for k,v in x.items() if k not in ['headers','request']} for x in rows],indent=2))
