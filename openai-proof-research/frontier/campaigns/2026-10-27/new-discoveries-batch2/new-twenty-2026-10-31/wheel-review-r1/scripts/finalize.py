from pathlib import Path
import json,hashlib,re,datetime
D=Path.cwd()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
before=json.loads((D/'receipts/inputs-before.json').read_text());after={p:sha(Path(p)) for p in before};assert before==after
(D/'receipts/inputs-after.json').write_text(json.dumps(after,indent=2))
manifest=json.loads((D/'replay/manifest.json').read_text())
assert all(sha(D/'replay'/p)==v for p,v in manifest.items())
mods=json.loads((D/'replay/modules.json').read_text());index=[];counts={}
for m in mods:
 for mode,name in [('build',m),('check',m),('audit','ReviewAudit'+m)]:
  r=json.loads((D/'logs'/(mode+'-'+name+'.log.receipt.json')).read_text());assert r['exit_code']==0 and r['killed_reason'] is None
 text=(D/'logs'/('audit-ReviewAudit'+m+'.log')).read_text();declarations=text.split('DECL ')[1:];counts[m]=len(declarations)
 assert int(re.search(r'TOTAL_LOCAL_DECLARATIONS (\d+)',text)[1])==counts[m]
 for chunk in declarations:
  name,rest=chunk.split('\n',1)
  typ=rest.split('TYPE ',1)[1].split('\nBODY_PRESENT',1)[0]
  kind=re.search(r'KIND (\w+)',rest)[1];body='BODY_PRESENT true' in rest
  axioms=re.search(r'AXIOMS \[(.*?)\]',rest)[1].split(', ');axioms=[x for x in axioms if x]
  assert 'UNSAFE false' in rest and 'PARTIAL false' in rest
  assert set(axioms)<={'propext','Classical.choice','Quot.sound'}
  assert body or kind in ['inductive','constructor','recursor']
  index.append(dict(name=name,module=m,type=typ,body_present=body,kind=kind,unsafe=False,partial=False,axioms=axioms))
assert len(index)==285
(D/'receipts/declarations.json').write_text(json.dumps(index,indent=2))
# Source lexical hunt separate from audit tooling.
scan={m:re.findall(r'\b(?:sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool|implemented_by|extern)\b',(D/'replay/formal'/(m+'.lean')).read_text()) for m in mods}
assert all(not v for v in scan.values());(D/'receipts/forbidden-source-scan.json').write_text(json.dumps(scan,indent=2))
rs=[json.loads(p.read_text()) for p in (D/'logs').glob('*.receipt.json')]
resource=dict(guarded_processes=len(rs),peak_sampled_private_rss_bytes=max(x['peak_sampled_private_rss_bytes'] for x in rs),max_subprocess_wall_seconds=max(x['wall_seconds'] for x in rs),all_guarded_caps_respected=all(x['killed_reason'] is None and x['wall_seconds']<140 and x['peak_sampled_private_rss_bytes']<=6*1024**3 for x in rs),systemd_scope='MemoryMax=6G',MALLOC_ARENA_MAX=2)
assert resource['all_guarded_caps_respected']
for n in ['False','WrongValue','NoRange']:
 r=json.loads((D/'logs'/('audit-ReviewNegative'+n+'.log.receipt.json')).read_text());assert r['exit_code']==1
for n in ['ReviewRestatement','ReviewSourceCorollary']:
 r=json.loads((D/'logs'/('audit-'+n+'.log.receipt.json')).read_text());assert r['exit_code']==0
report={'371637':dict(review_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),role='independent adversarial reviewer; root alone accepts',candidate='arXiv:2511.18747 Conjecture 7.3',endpoint='WheelFormal.target_proved : WheelFormal.Target',packet_sha256=before[str(D.parent/'wheel-formal-r2b/wheel-complete-source.zip')],gates={
 'A':dict(verdict='PASS',reason='Faithful Cartesian wheel square and literal fractional colouring infimum for t >= 1; source nontrivial scope t >= 2; no t = 0 claim.'),
 'B':dict(verdict='PASS',reason='Uniform pairing and weighted bound correct; independent rational LP certificates t = 1..4 and exhaustive family independence/coverage t = 1..6 pass.',lp_receipt='receipts/independent-lp.json',coverage_receipt='receipts/independent-coverage.json'),
 'C':dict(verdict='PASS',strict_modules=14,leanchecker_modules=14,all_local_declarations=285,counts_by_module=counts,restatement='replay/formal/ReviewRestatement.lean',negative_controls=3,axioms=['propext','Classical.choice','Quot.sound'],declaration_index='receipts/declarations.json'),
 'D':dict(verdict='QUALIFIED_PASS',reason='No separate explicit uniform proof found in bounded live search; source-lemma subsumption is an affirmative objection, not novelty clearance.',limits=['Path screening is not full registry body screening.','Author searches partly timed out; no retries.','Other branches, unnamed works and older primary ultimate-independence bodies remain unread.'],live_heads={n:json.loads((D/'receipts'/(n+'-head.body')).read_text())['sha'] for n in ['openai','omega','authors']}),
 'E':dict(verdict='FAIL',reason='Source Lemma 4.2 applied in both coordinate directions and added yields the entire weighted lower bound. With source profiles, this endpoint is a routine corollary excluded by campaign rules.')},objections=[dict(id='E1',severity='disqualifying for campaign significance',source='arXiv:2511.18747v1 Lemma 4.2',derivation='n <= tm+1+(1-t)a and n <= tm+1+(1-t)b imply 2n+(t-1)(a+b) <= 2(tm+1). Left side equals candidate weight(I).',scope='t >= 2; t = 1 is routine K4 square.',arithmetic_certificate='replay/formal/ReviewSourceCorollary.lean')],recommendation='REJECT_CAMPAIGN_CREDIT',credit=0,next_actions=['Root should reconcile source Lemma 4.2 subsumption before any acceptance.','Retain the correct formal certificate as formalization work; do not count it as a new significant discovery.'],input_hashes_unchanged=True,source_manifest_verified=True,resource_receipts=resource,report='REVIEW.md')}
(D/'review.json').write_text(json.dumps(report,indent=2))
(D/'receipts/final-summary.json').write_text(json.dumps(dict(declarations=len(index),counts=counts,resources=resource,input_hashes_unchanged=True,source_manifest_verified=True),indent=2))
print(json.dumps(dict(declarations=len(index),resources=resource)))
