import json,hashlib,datetime,pathlib,sys
C=pathlib.Path(sys.argv[1]).resolve(); B=C.parent
TAGS=B/'lanes/pi-mathdb-full-corpus-inventory-r301/tags/screening-tags.jsonl'
Q=B/'lanes/root-mathdb-breadth-intake-r729/routing-queue.jsonl'
COV=B/'lanes/root-mathdb-breadth-intake-r729/coverage-delta.json'
MAN=B/'lanes/pi-mathdb-full-corpus-inventory-r301/manifest.json'
OLDL=B/'ledger.json'; L=C/'ledger.json'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
prev=json.loads((C/'expanded-corpus-r59/reservation.json').read_text())
for p,d in prev['input_hashes'].items():
    assert h(pathlib.Path(p))==d,p
queue={json.loads(x)['mathdb_id'] for x in Q.read_text().splitlines() if x.strip()}
cov={int(k) for k in json.loads(COV.read_text())}
excl=set(prev['excluded_ids'])
assigned=set()
for r in sorted(C.glob('*/reservation.json')):
    try: assigned|=set(json.loads(r.read_text()).get('ids',[]))
    except Exception: pass
led=json.loads(L.read_text())
for c in led['candidates']: assigned.add(int(c['mathdb_id']))
for ln in led['lanes']: assigned|=set(ln.get('ids',[]))
for f in led['followups']: assigned|=set(int(x) for x in f.get('initial_targets',[]) if str(x).isdigit())
def eligible(r):
    return r['status']=='open' and r['post_type']=='conjecture' and r['statement_completeness']=='full'
rows=[json.loads(x) for x in TAGS.read_text().splitlines() if x.strip()]
bad=queue|cov|excl|assigned
el=[r for r in rows if eligible(r) and r['mathdb_id'] not in bad]
# reproduce r59 selection rule as sanity check
el59=[r for r in rows if eligible(r) and r['mathdb_id'] not in (queue|cov|excl) and r['review_priority_score']==38 and 364118<r['mathdb_id']]
sel59=[r['mathdb_id'] for r in sorted(el59,key=lambda r:r['mathdb_id'])][:40]
print('r59 rule reproduces:',sel59==prev['ids'])
top=max(r['review_priority_score'] for r in el)
el.sort(key=lambda r:(-r['review_priority_score'],r['mathdb_id']))
pick=el[:40]
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
out={'utc':now,'kind':prev['kind'],'ids':[r['mathdb_id'] for r in pick],'rows':pick,
 'input_hashes':{str(p):h(p) for p in [COV,Q,TAGS,MAN,OLDL]},
 'mutable_campaign_ledger_snapshot':{'path':str(L),'sha256':h(L),'utc':now},
 'excluded_ids':sorted(bad),'eligible_metadata_rows_after_filters':len(el),
 'selection':prev['selection'],'limitation':prev['limitation'],'output_requirement':prev['output_requirement'],
 'max_remaining_score':top,'score_set':sorted({r['review_priority_score'] for r in pick})}
pathlib.Path(sys.argv[2]).write_text(json.dumps(out,indent=2,ensure_ascii=False))
print(len(el),top,out['ids'][0],out['ids'][-1],out['score_set'])
for r in pick: print(r['mathdb_id'],r['title'][:100])
