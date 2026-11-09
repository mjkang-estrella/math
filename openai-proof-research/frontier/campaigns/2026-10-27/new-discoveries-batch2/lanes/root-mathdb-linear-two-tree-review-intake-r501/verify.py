from pathlib import Path
import hashlib,json,sys
from datetime import datetime,timezone
R=Path(__file__).resolve().parent;L=R.parent;C=R/'frozen/sol-mathdb-linear-two-tree-source-prior-review-r498';BASE=R/'frozen/root-mathdb-abelianisation-retirement-intake-r499'
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check(p,r):assert p.is_file() and p.stat().st_size==r.get('size',r.get('bytes')) and sha(p)==r['sha256'],str(p)
def names(p,exc):return {str(x.relative_to(p)) for x in p.rglob('*') if x.is_file()}-set(exc)
def put(n,x):(R/n).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
bindings=read(R/'bindings.json')
for r in bindings:check(Path(r['original']),r);check(Path(r['copy']),r)
m=read(C/'manifest.json');exc={'manifest.json','final-receipt.json'}
assert set(m['excluded_exact_paths'])==exc and len(m['files'])==28
assert names(C,exc)=={r['path'] for r in m['files']}==names(L/C.name,exc)
for r in m['files']:check(C/r['path'],r)
refs=read(C/'flat-original-bindings.json')['files'];assert len(refs)==19
for r in refs:check(Path(r['path']),r)
receipt=read(C/'final-receipt.json');assert receipt['integrity']=='PASS' and receipt['manifest']['sha256']==sha(C/'manifest.json') and receipt['prior']=='HOLD' and receipt['substantive']=='NOT CLEARED'
assert receipt['counts']=={'additional':9,'total':39,'next':40}
coverage=read(BASE/'coverage-delta.json');assert len(coverage)==3683
hypotheses=read(BASE/'hypothesis-queue.json')
for h in hypotheses:
 if h['mathdb_id']==337963:h.update(status='mathematics_reported_pass_prior_substantive_hold',next_review_lane='sol-mathdb-linear-two-tree-prior-boundary-r502')
outputs={'coverage-delta.json':coverage,'adjudications.json':read(BASE/'adjudications.json'),'hypothesis-queue.json':hypotheses,'active-breadth-reservations.json':[read(BASE/'reserved-ids.json')]}
ownexc={'manifest.json','verification-receipt.json'}
if sys.argv[1:]==['build']:
 for n,x in outputs.items():put(n,x)
 put('manifest.json',{'files':[{'path':s,'size':(R/s).stat().st_size,'sha256':sha(R/s)} for s in sorted(names(R,ownexc))],'excluded_exact_paths':sorted(ownexc)})
elif sys.argv[1:]==['verify']:
 for n,x in outputs.items():assert read(R/n)==x
 own=read(R/'manifest.json')['files'];assert names(R,ownexc)=={r['path'] for r in own}
 for r in own:check(R/r['path'],r)
 put('verification-receipt.json',{'status':'PASS','utc':datetime.now(timezone.utc).isoformat(),'root_bindings':len(bindings),'review_payloads':28,'review_flat_references':19,'reported_statement_reviews':3683,'accepted_counts':[9,39,40],'root_math_replay':False,'scope':'integrity only; reviewer math report retained, prior/substantive HOLD'})
else:raise SystemExit('build or verify')
print('PASS',sys.argv[1],len(bindings),'root binding pairs')
