"""Read-only independent validation, except final receipt; no upstream verifier imports."""
import sys,pathlib,hashlib,json,datetime
ROOT=pathlib.Path('/home/mj-kang/Documents/Dev/math');BASE=ROOT/'openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes';HERE=pathlib.Path(__file__).resolve().parents[1];errors=[];nchecks=0

def verify(p,h,n=None):
 global nchecks
 nchecks+=1
 try:
  size=p.stat().st_size;d=hashlib.sha256()
  with p.open('rb') as f:
   while True:
    block=f.read(262144)
    if not block:break
    d.update(block)
  if d.hexdigest()!=h or n is not None and size!=n:errors.append('mismatch '+str(p))
 except Exception as ex:errors.append('unreadable '+str(p)+' '+str(ex))

def require(ok,msg):
 if not ok:errors.append(msg)

def load(p):return json.loads(p.read_text())

for name in ('bindings.json','original-bindings.json'):
 for x in load(HERE/name)['files']:verify(ROOT/x['path'],x['sha256'],x['bytes'])
for lane in ('root-mathdb-breadth-intake-r469','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363','pi-mathdb-full-corpus-inventory-r301'):
 folder=BASE/lane;manifest=load(folder/'manifest.json');entries=manifest if isinstance(manifest,list) else manifest['files']
 for x in entries:verify(folder/x['path'],x['sha256'],x.get('bytes',x.get('size')))
 if lane.startswith('pi-'):
  chunks=[x for x in entries if x['path'].startswith('corpus/mathdb-normalized-chunk-')];require(len(chunks)==20,'not twenty chunks')
  frozen=manifest['frozen_inputs'];require(len(frozen)==8,'not eight frozen_inputs')
  for x in frozen:verify(folder/x['path'],x['sha256'],x['bytes'])
 else:
  for x in load(folder/'bindings.json'):
   verify(pathlib.Path(x['original']),x['sha256'],x.get('size'))
   copy=pathlib.Path(x['copy']);copy=copy if copy.is_absolute() else folder/copy
   verify(copy,x['sha256'],x.get('size'))
intake=BASE/'root-mathdb-breadth-intake-r469';reservation=load(intake/'reserved-ids.json');wanted=set(reservation['ids']);require(len(wanted)==50,'assignment size');require(wanted=={x['mathdb_id'] for x in load(intake/'queue.json')},'queue mismatch');require(not wanted.intersection(reservation['other_active_reservations']),'active overlap')
coverage=load(intake/'coverage-delta.json');require(len(coverage)==3083 and all(x.get('record_statement_review') for x in coverage.values()),'baseline report mismatch');require(not wanted.intersection(map(int,coverage)),'prior coverage overlap');require(not wanted.intersection({372627,372628,368940,404067,364119}),'explicit exclusion overlap')
accepted=load(BASE/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json');require(not wanted.intersection(map(int,accepted['mathdb_lookup'])),'accepted overlap')
history=load(BASE/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json');associated=set()
def associations(v):
 if isinstance(v,dict):
  for k,t in v.items():
   if ('mathdb' in k or k in ('problem_ids','problem_id')):
    vals=t if isinstance(t,list) else [t]
    for z in vals:
     if isinstance(z,(int,str)) and str(z).isdigit():associated.add(int(z))
   associations(t)
 elif isinstance(v,list):
  for t in v:associations(t)
associations(history);associations(accepted);require(not wanted.intersection(associated),'historical association overlap')
dispositions=load(HERE/'dispositions.json');require(len(dispositions)==50 and {d['mathdb_id'] for d in dispositions}==wanted,'disposition assignment mismatch');seen=set()
for d in dispositions:
 p=ROOT/d['original_chunk'];line=d['original_line']
 with p.open('rb') as f:
  raw=next((b for i,b in enumerate(f,1) if i==line),None)
 require(raw is not None,'line missing')
 if raw is None:continue
 r=json.loads(raw);require(r['mathdb_id']==d['mathdb_id'],'original id mismatch');require(r['statement']==d['literal_statement'],'literal mismatch');require(hashlib.sha256(raw).hexdigest()==d['original_line_sha256'],'line hash mismatch');require(hashlib.sha256(r['statement'].encode('utf-8')).hexdigest()==d['statement_utf8_sha256'],'statement hash mismatch');canonical=json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode();require(hashlib.sha256(canonical).hexdigest()==d['canonical_record_sha256'],'canonical record mismatch');require(d['accepted_credit']==0 and not d['novelty_pass'],'unwarranted credit');seen.add(r['mathdb_id'])
require(seen==wanted,'not all originals read')
for s in load(HERE/'retained-sources.json'):
 require(s['status']=='retained','source retrieval failure');verify(HERE/s['path'],s['sha256'],s['bytes']);verify(HERE/s['text_path'],s['text_sha256']);require(bool(s['requested_utc']) and bool(s['embedded_arxiv_version']),'missing source provenance')
require(load(HERE/'proposals.json')['proposals']==[],'unexpected proposal')
manifest_path=HERE/'manifest.json'
if manifest_path.exists():
 payload=load(manifest_path);require(payload['excluded_exact_relative_paths']==['manifest.json','final-receipt.json'],'exclusions differ')
 actual={str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file() and str(p.relative_to(HERE)) not in {'manifest.json','final-receipt.json'}}
 expected={x['path'] for x in payload['files']};require(len(expected)==len(payload['files']) and actual==expected,'exact payload file set mismatch')
 for x in payload['files']:verify(HERE/x['path'],x['sha256'],x['bytes'])
 if '--negative' in sys.argv:
  # Deliberately incorrect digest must add a real mismatch and force nonzero exit.
  x=payload['files'][0];verify(HERE/x['path'],'0'*64,x['bytes'])
else:
 require('--preseal' in sys.argv,'missing payload manifest')
 if '--negative' in sys.argv:verify(HERE/'SUMMARY.md','0'*64)
result=dict(status='PASS' if not errors else 'FAIL',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),independent_checks=nchecks,errors=errors,scope='integrity only; no mathematical/novelty acceptance',assignment=50,inventory_chunks=20,inventory_separately_listed_frozen_inputs=8,proposal_count=0,credit=0)
if '--receipt' in sys.argv:
 result['manifest_sha256']=hashlib.sha256(manifest_path.read_bytes()).hexdigest();(HERE/'final-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2));sys.exit(0 if not errors else 1)
