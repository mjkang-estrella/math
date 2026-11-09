"""Merge completed checker batches; only current local certificate hashes survive."""
import sys
sys.dont_write_bytecode = True
import os, glob, json, hashlib
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0,HERE)
from breadth import atomic_json
certs = {}
for fn in glob.glob(os.path.join(HERE,'certs','**','*.jsonl'),recursive=True):
    h = hashlib.sha256()
    with open(fn,'rb') as f:
        for block in iter(lambda:f.read(1<<20),b''): h.update(block)
    certs[os.path.relpath(fn,HERE)] = h.hexdigest()
merged = {}
for fn in sorted(glob.glob(os.path.join(HERE,'checker_results*.json'))):
    for key,rec in json.load(open(fn)).items():
        if certs.get(rec['file']) != rec['sha256']: continue
        old = merged.get(key)
        if old is None or rec['status']=='PASS' or old['status']!='PASS': merged[key]=rec
atomic_json(os.path.join(HERE,'checker_results.json'),merged)
print('certificates',len(certs),'checker records',len(merged),
      {s:sum(r['status']==s for r in merged.values()) for s in ('PASS','FAIL','BUDGET')})
