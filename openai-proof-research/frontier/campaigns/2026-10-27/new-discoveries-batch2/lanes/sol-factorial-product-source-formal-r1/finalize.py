import hashlib,json,subprocess,sys
from pathlib import Path
R=Path(__file__).resolve().parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b)
 return h.hexdigest()
frozen=json.loads((R/'frozen-before.json').read_text())
helper=next(Path(r['original']) for r in frozen if Path(r['original']).name=='helper_guard.py')
r=subprocess.run([sys.executable,str(helper),sys.executable,str(R/'verify.py')],capture_output=True,text=True)
assert r.returncode==0,r.stderr
replay=json.loads((R/'replay-fresh/replay-receipt.json').read_text())
assert replay['status']=='LITERAL_GAMMA_SOURCE_REFUTATION_PASS'
assert replay['declaration_count']==31
assert replay['archive_sha256']==sha(R/'source-only.zip')
assert (R/'logs/FullAudit.log').read_bytes()==(R/'replay-fresh/logs/FullAudit.log').read_bytes()
assert (R/'logs/FactorialProduct.log').stat().st_size==0
for row in frozen:
 assert sha(Path(row['original']))==row['sha256']
 if 'copy' in row:assert sha(R/row['copy'])==row['sha256']
names=['SUMMARY.md','PROVENANCE.md','FAILURES.md','README.md','manifest.json','source-only.zip',
 'archive-receipt.json','frozen-before.json','frozen-after.json','replay-fresh/replay-receipt.json',
 'replay-fresh/frozen-after.json','logs/FactorialProduct.log','logs/FullAudit.log',
 'replay-fresh/logs/FactorialProduct.log','replay-fresh/logs/FullAudit.log']
result={'status':'COMPLETE_LITERAL_SOURCE_ENDPOINT','formal_pass':True,
 'independent_final_review_performed':False,'root_acceptance_asserted':False,
 'source_only_extracted_replay_pass':True,'declaration_count':31,
 'local_and_extracted_audits_byte_identical':True,'no_residual_endpoint_hypotheses':True,
 'frozen_originals_unchanged':True,'pins_and_lockfile_verified':True,
 'allowed_axioms':['propext','Classical.choice','Quot.sound'],
 'receipt_and_artifact_hashes':{n:sha(R/n) for n in names}}
(R/'FINAL-RECEIPT.json').write_text(json.dumps(result,indent=2)+'\n')
files=names+['FINAL-RECEIPT.json','finalize.py']
(R/'delivery-manifest.json').write_text(json.dumps({n:sha(R/n) for n in files},indent=2)+'\n')
print(json.dumps(result,indent=2))
