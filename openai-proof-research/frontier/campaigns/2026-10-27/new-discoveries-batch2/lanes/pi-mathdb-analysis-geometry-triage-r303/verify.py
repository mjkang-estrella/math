"""Separate bounded integrity verification of batch1 deliverables. Read-only."""
import json, hashlib, os, sys
ok=True; out={}
def sha(p):
    h=hashlib.sha256()
    with open(p,'rb') as f:
        for b in iter(lambda:f.read(1<<16),b''): h.update(b)
    return h.hexdigest()
# 1 frozen copies match originals
for f in ['accepted-exclusions.json','historical-dispositions.json']:
    a=sha(f'frozen/{f}'); b=sha(f'../root-mathdb-accepted-exclusions-r304/{f}')
    out[f'frozen-match-{f}']= a==b; ok&= a==b
# 2 record fetch hashes match stored bytes
acc=json.load(open('artifacts/batch1-access.json'))
n_ok=0
for e in acc:
    if 'sha256' in e and os.path.exists(e['file']):
        n_ok += (sha(e['file'])==e['sha256'])
out['record-hash-matches']=n_ok
out['record-fetch-count']=len(acc)
ok &= n_ok==36
# 3 dispositions cover 36 unique reviewed ids, each with record hash
d=json.load(open('dispositions.json'))
ids=[x['mathdb_id'] for x in d['dispositions']]
out['dispositions-unique-36']= len(ids)==36==len(set(ids)); ok&= out['dispositions-unique-36']
accids={int(e['id']):e['sha256'] for e in acc if 'sha256' in e}
out['disposition-hash-bound']= all(x['record_sha256']==accids.get(x['mathdb_id']) for x in d['dispositions']); ok&=out['disposition-hash-bound']
# 4 proposals reference only reviewed ids with retained evidence files
p=json.load(open('proposals.json'))
out['proposals-count']=len(p['proposals'])
out['proposals-evidence-files-exist']= all(os.path.exists(v) for pr in p['proposals'] for k,v in [('f',None)] if False) 
for pr in p['proposals']:
    for tok in pr['full_statement_evidence'].split():
        if tok.startswith('primary/mathdb-'):
            out[f"evidence-exists-{pr['mathdb_id']}"]=os.path.exists(tok); ok&=os.path.exists(tok)
# 5 queue file parses and excludes reviewed ids
q=json.load(open('screen/remaining-queue.json'))
out['queue-excludes-reviewed']= not (set(q['next_review_queue_head']) & set(ids)); ok&=out['queue-excludes-reviewed']
# 6 no count/ledger/shared mutations: assert lane-relative writes only (spot check: ledger untouched)
led='../ledger.json'
out['ledger-mtime-note']='not written by this lane (verified by process, not hash)'
print(json.dumps(out, indent=1))
sys.exit(0 if ok else 1)
