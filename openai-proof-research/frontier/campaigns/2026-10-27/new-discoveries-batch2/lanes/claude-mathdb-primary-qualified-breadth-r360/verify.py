# Fail-nonzero verifier for claude-mathdb-primary-qualified-breadth-r360.
# Usage: python3 -B verify.py [LANE_DIR] [LANES_PARENT]   (defaults: this file's dir and its parent)
import sys,json,hashlib,subprocess,datetime,os
from pathlib import Path
L=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else Path(__file__).resolve().parent
B=Path(sys.argv[2]).resolve() if len(sys.argv)>2 else L.parent
fails=[]
def chk(c,msg):
    if not c: fails.append(msg)
def h(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ents(m): return m['files'] if isinstance(m,dict) else m
# 1 own manifest
M=json.loads((L/'manifest.json').read_text()); EX=set(M['excluded'])
chk(EX=={'manifest.json','verification-receipt.json'},'manifest exclusions')
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-EX
chk(actual=={e['path'] for e in M['files']},'payload set mismatch: %s'%sorted(actual^{e['path'] for e in M['files']})[:5])
for e in M['files']:
    p=L/e['path']; chk(p.exists() and p.stat().st_size==e['size'] and h(p)==e['sha256'],'hash '+e['path'])
# 2 flat input bindings, re-hashed in place
IB=json.loads((L/'input-bindings.json').read_text())
for r in IB: chk(Path(r['path']).exists() and h(r['path'])==r['sha256'] and Path(r['path']).stat().st_size==r['size'],'binding '+r['path'])
# 3 originals vs their manifests, in place
P=B/'pi-mathdb-full-corpus-inventory-r301'; n=0
for e in ents(json.loads((P/'manifest.json').read_text())):
    if e['path'].startswith('corpus/'): n+=1; chk(h(P/e['path'])==e['sha256'] and (P/e['path']).stat().st_size==e.get('size',e.get('bytes')),'corpus '+e['path'])
chk(n==20,'corpus chunk count')
for name in ['root-mathdb-gram-intake-r359','root-mathdb-breadth-intake-r355','root-mathdb-accepted-exclusions-r304']:
    for e in ents(json.loads((B/name/'manifest.json').read_text())):
        chk(h(B/name/e['path'])==e['sha256'],name+' '+e['path'])
R=B/'root-mathdb-gram-intake-r359'
for e in json.loads((R/'bindings.json').read_text()): chk(h(e['original'])==e['sha256'],'r359 binding original '+e['original'])
# 4 IDs and disjointness
ids=json.loads((R/'reserved-ids.json').read_text())['ids']; cov=json.loads((R/'coverage-delta.json').read_text())
other=json.loads((B/'root-mathdb-breadth-intake-r355/reserved-ids.json').read_text())['ids']
chk(len(set(ids))==50 and not set(map(str,ids))&set(cov) and not set(ids)&set(other) and len(cov)==533,'disjointness')
# 5 records re-derived from corpus in place
recs=json.loads((L/'records.json').read_text()); chk([r['mathdb_id'] for r in recs]==ids,'records order')
lines={}
for r in recs: lines.setdefault(r['corpus_path'],set()).add(r['corpus_line'])
cache={}
for f,ls in lines.items():
    for i,line in enumerate(open(f,encoding='utf-8'),1):
        if i in ls: cache[(f,i)]=json.loads(line)
for r in recs:
    c=cache.get((r['corpus_path'],r['corpus_line']))
    chk(c is not None and c['mathdb_id']==r['mathdb_id'] and c['statement']==r['statement'] and hashlib.sha256(c['statement'].encode()).hexdigest()==r['literal_statement_sha256'],'record %s'%r['mathdb_id'])
    chk(all(c.get(k)==v for k,v in r.items() if k not in ('corpus_path','corpus_line','literal_statement_sha256')) if c else False,'record fields %s'%r['mathdb_id'])
# 6 dispositions / proposals
D=json.loads((L/'dispositions.json').read_text())['dispositions']; rs={r['mathdb_id']:r for r in recs}
chk([d['mathdb_id'] for d in D]==ids,'disposition ids/order')
for d in D:
    chk(d['literal_statement_sha256']==rs[d['mathdb_id']]['literal_statement_sha256'],'disp hash %s'%d['mathdb_id'])
    chk(d['accepted_credit']==0 and d['prior_cleared'] is False and d['novelty_review']=='not cleared' and d['reason'] and d['evidence_level'],'disp fields %s'%d['mathdb_id'])
PR=json.loads((L/'proposals.json').read_text())['proposals']
chk(len(PR)<=3 and all(p['credit']==0 for p in PR),'proposals cap/credit')
chk({p['mathdb_id'] for p in PR}=={d['mathdb_id'] for d in D if d['disposition']=='promising-brief'},'proposals vs briefs')
for p in PR: chk((L/p['brief']).exists() and p['literal_statement_sha256']==rs[p['mathdb_id']]['literal_statement_sha256'],'brief '+p['brief'])
# 7 retained sources match provenance
for r in json.loads((L/'source-provenance.json').read_text()):
    b=L/'sources'/r['name']/'body'
    if 'sha256' in r: chk(b.exists() and h(b)==r['sha256'] and b.stat().st_size==r['size'],'source '+r['name'])
# 8 regenerate decisive certificates and re-run the exact identity check
env=dict(os.environ,OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1')
def run(args):
    return subprocess.run([sys.executable,'-B',str(L/'checks'/args[0])]+args[1:],capture_output=True,text=True,env=env,timeout=200)
for t,K in [(3,11),(3,12),(5,14)]:
    rec=json.loads((L/'runs'/f'lab321_t{t}_K{K}.stdout').read_text().splitlines()[0])
    out=run(['lab321_period.py',str(t),str(K)]); chk(out.returncode==0,'period run %d %d'%(t,K))
    new=json.loads(out.stdout.splitlines()[0]) if out.returncode==0 else {}
    chk(new.get('certificate_sha256')==rec['certificate_sha256'],'certificate regen %d %d'%(t,K))
    if t==3: chk(h(L/'certificates'/f'lab321_t3_K{K}.json')==rec['certificate_sha256'],'stored cert %d'%K)
    if (t,K)==(3,12): chk(new.get('period_size_histogram')=={'p12_s12':2},'t3 K12 structure')
    if (t,K)==(3,11): chk(new.get('period_size_histogram')=={},'t3 K11 acyclic')
    if (t,K)==(5,14): chk(new.get('all_periods_even') is True,'t5 K14 even periods')
chk(run(['c368940_inclusion_inverse.py']).returncode==0,'368940 identity')
chk(run(['lab321_upper_lean.py','3','13','142','0','12','0,5,10,3,8,1,6,11,4']).returncode==0,'372627 upper bound replay')
res={'status':'PASS' if not fails else 'FAIL','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lane':str(L),
 'manifest_files':len(M['files']),'input_bindings_rehashed':len(IB),'corpus_chunks_verified_in_place':n,'records_rederived':len(recs),
 'dispositions':len(D),'proposals':len(PR),'certificates_regenerated':3,'credit':0,'counts_unchanged':'9 additional / 39 total / next 40','failures':fails[:50]}
if len(sys.argv)<=1: (L/'verification-receipt.json').write_text(json.dumps(res,indent=1)+'\n')
print(json.dumps(res)); sys.exit(0 if not fails else 1)
