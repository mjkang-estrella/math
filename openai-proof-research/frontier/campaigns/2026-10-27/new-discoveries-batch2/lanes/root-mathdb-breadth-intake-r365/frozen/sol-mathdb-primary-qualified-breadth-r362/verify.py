from pathlib import Path
import hashlib,json,datetime,math
from fractions import Fraction
R=Path(__file__).resolve().parent;L=R.parent
EX={'manifest.json','verification-receipt.json'}
def require(x,msg):
 if not x:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def check(p,h,s=None):
 b=p.read_bytes();require(sha(b)==h,'SHA256 mismatch: '+str(p))
 if s is not None:require(len(b)==s,'size mismatch: '+str(p))
def load(p):return json.loads(p.read_text())
manifest=load(R/'manifest.json')['files']
actual={str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()}-EX
require(actual=={e['path'] for e in manifest} and len(actual)==len(manifest),'payload exact set')
for e in manifest:check(R/e['path'],e['sha256'],e['size'])
refs=load(R/'input-bindings.json')
for e in refs:check(Path(e['path']),e['sha256'],e['size'])
I=L/'root-mathdb-breadth-intake-r361'
for e in load(I/'manifest.json')['files']:check(I/e['path'],e['sha256'],e['size'])
a=load(I/'reserved-ids.json')['ids'];q=load(I/'queue.json');other=load(L/'root-mathdb-gram-intake-r359/reserved-ids.json')['ids']
require(len(a)==len(set(a))==len(other)==len(set(other))==50,'reservation cardinality')
require(not set(a)&set(other),'reservation overlap')
require({x['mathdb_id'] for x in q}==set(a) and len(q)==50,'queue ids')
require(len(load(I/'coverage-delta.json'))==583,'incoming coverage')
freeze=load(R/'freeze-receipt.json');require(freeze['ids']==a and freeze['other_ids']==other,'reservation change')
C=L/'pi-mathdb-full-corpus-inventory-r301'
chunks=[e for e in load(C/'manifest.json')['files'] if e['path'].startswith('corpus/')]
require(len(chunks)==20,'corpus chunks')
found={};count={n:0 for n in a}
for e in chunks:
 check(C/e['path'],e['sha256'],e['bytes'])
 for line in (C/e['path']).read_text().splitlines():
  x=json.loads(line);n=int(x.get('mathdb_id',x.get('id',0)))
  if n in count:found[n]=x;count[n]+=1
require(set(found)==set(a) and all(v==1 for v in count.values()),'corpus record exact set/unique')
records=load(R/'records.json');require(len(records)==50 and {x['mathdb_id'] for x in records}==set(a),'retained records exact set')
for x in records:require(x==found[x['mathdb_id']],'record extraction mismatch')
D=L/'root-mathdb-accepted-exclusions-r304'
for e in load(D/'manifest.json'):
 if e['path'] in {'accepted-exclusions.json','historical-dispositions.json','README.md'}:check(D/e['path'],e['sha256'])
d=load(R/'dispositions.json')['dispositions'];require(len(d)==50 and {x['mathdb_id'] for x in d}==set(a),'disposition exact set')
require(len({x['individual_reason'] for x in d})==50,'individual reasons')
for x in d:
 require(x['literal_statement']==found[x['mathdb_id']]['statement'],'literal statement mismatch')
 require(sha(x['literal_statement'].encode())==x['literal_statement_sha256'],'statement SHA256')
 require(x['accepted_credit']==0 and not x['prior_cleared'] and not x['source_scope_cleared'],'unearned qualification')
require(sum(x['primary_body_review'] for x in d)==4,'primary count')
require(sum(x['concluding_proof_section_read'] for x in d)==1,'proof section count')
require(not any(x['full_resolution_proof_body_read'] or x['complete_dependencies_read'] for x in d),'proof-depth count')
require(load(R/'proposals.json')==[],'eligible proposals must be empty')
for log in ['source-provenance.json','successor-provenance.json','current-body-provenance.json']:
 for e in load(R/log):
  check(R/e['path'],e['sha256'],e['size']);require(e['url'].startswith('https://') and e['utc'] and e['version'],'source provenance')
checks=load(R/'bounded-checks.json')['checks'];require([x['N'] for x in checks]==list(range(1,33)),'bounded checks set')
for x in checks:require(x['pass_exact'] and Fraction(x['coefficient'])==Fraction(1,math.factorial(x['N']-1)),'exact rational check')
ledger=load(L.parent/'ledger.json');require((ledger['accepted_count'],ledger['total_accepted_count'],ledger['next_global_outcome_number'])==(9,39,40),'counts changed')
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha((R/'manifest.json').read_bytes()),payload_files=len(manifest),original_input_bindings=len(refs),corpus_chunks_rehashed=20,exact_dispositions=50,other_reservations=50,sets_disjoint=True,primary_statement_body_screens=4,concluding_proof_sections_read=1,complete_resolution_proof_bodies_and_dependencies_read=0,eligible_proposals=0,credit=0,mathdb_requests=0,mathematical_acceptance=False,lean_replay=False)
(R/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
