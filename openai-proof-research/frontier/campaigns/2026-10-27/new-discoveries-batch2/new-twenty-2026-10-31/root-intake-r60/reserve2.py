# Same eligibility/exclusions as reserve.py (which reproduces the r59 rule); within the top remaining score,
# prioritise finitely-checkable combinatorial records: witness/construction cues and discrete-math MathDB tags.
import json,hashlib,datetime,pathlib,sys,glob
C=pathlib.Path(sys.argv[1]).resolve(); B=C.parent
sys.argv=[sys.argv[0],str(C),'/dev/null']
import runpy
TAGS=B/'lanes/pi-mathdb-full-corpus-inventory-r301/tags/screening-tags.jsonl'
Q=B/'lanes/root-mathdb-breadth-intake-r729/routing-queue.jsonl'
COV=B/'lanes/root-mathdb-breadth-intake-r729/coverage-delta.json'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
prev=json.loads((C/'expanded-corpus-r59/reservation.json').read_text())
queue={json.loads(x)['mathdb_id'] for x in Q.read_text().splitlines() if x.strip()}
cov={int(k) for k in json.loads(COV.read_text())}
excl=set(prev['excluded_ids']); assigned=set()
for r in C.glob('*/reservation.json'):
    try: assigned|=set(json.loads(r.read_text()).get('ids',[]))
    except Exception: pass
led=json.loads((C/'ledger.json').read_text())
for c in led['candidates']: assigned.add(int(c['mathdb_id']))
for f in led['followups']: assigned|=set(int(x) for x in f.get('initial_targets',[]) if str(x).isdigit())
bad=queue|cov|excl|assigned
rows=[json.loads(x) for x in TAGS.read_text().splitlines() if x.strip()]
el=[r for r in rows if r['status']=='open' and r['post_type']=='conjecture' and r['statement_completeness']=='full' and r['mathdb_id'] not in bad]
scores=sorted({r['review_priority_score'] for r in el},reverse=True); top=scores[0]; pool=[]
for sc in scores:
    pool+= [r for r in el if r['review_priority_score']==sc]
    if len(pool)>=200: break
ids={r['mathdb_id'] for r in pool}; mtags={}
for ch in sorted(glob.glob(str(B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus/mathdb-normalized-chunk-*.jsonl'))):
    for line in open(ch,encoding='utf8'):
        try: d=json.loads(line)
        except Exception: continue
        if d.get('mathdb_id') in ids: mtags[d['mathdb_id']]=d.get('tags') or []
DISC=('graph','combinator','extremal','coloring','colouring','ramsey','hypergraph','tree','matching','design','code','permutation','tournament','digraph','word','partition','poset','matroid','finite-geometry','additive','sumset','domination','spectral')
def key(r):
    t=set(r['screening_tags']); mt=' '.join(mtags.get(r['mathdb_id'],[])).lower()
    return (-r['review_priority_score'], -('counterexample_or_witness_cue' in t), -('explicit_construction_or_example_request' in t), -any(k in mt for k in DISC), -('few_quantified_parameters' in t), r['mathdb_id'])
pool.sort(key=key); import os; pick=pool[:int(os.environ.get("RESERVE_N","40"))]
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
out={'utc':now,'kind':prev['kind'],'ids':[r['mathdb_id'] for r in pick],'rows':[dict(r,mathdb_tags=mtags.get(r['mathdb_id'],[])) for r in pick],
 'input_hashes':{str(p):h(p) for p in [COV,Q,TAGS]},'excluded_ids_count':len(bad),'eligible_metadata_rows_after_filters':len(el),'top_score':top,'top_score_pool':len(pool),
 'selection':'Same eligibility and exclusions as earlier expanded-corpus reservations; within the top remaining score, prioritise counterexample/witness cue, explicit construction cue, discrete-mathematics MathDB tags, few-parameter cue, then ID.',
 'limitation':prev['limitation'],'output_requirement':prev['output_requirement']}
pathlib.Path(sys.argv[2] if len(sys.argv)>2 else '/dev/stdout')
pathlib.Path(OUT).write_text(json.dumps(out,indent=2,ensure_ascii=False)) if False else None
print(json.dumps({'pool':len(pool),'top':top}))
json.dump(out,open(OUTPATH,'w'),indent=2,ensure_ascii=False) if False else None
globals()['RESULT']=out
