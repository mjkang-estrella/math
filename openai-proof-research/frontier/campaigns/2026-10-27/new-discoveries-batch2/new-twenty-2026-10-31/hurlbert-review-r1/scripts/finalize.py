from pathlib import Path
import json,hashlib,re,datetime
D=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert (D/'inputs-before.sha256').read_bytes()==(D/'inputs-after.sha256').read_bytes()
assert len((D/'logs/inventory.log').read_text().splitlines())==13
for line in (D/'logs/axioms.log').read_text().splitlines():
 if 'depends on axioms:' in line:
  ax=re.search(r'\[([^]]*)\]',line)[1];assert set(ax.split(', '))<={'propext','Classical.choice','Quot.sound'}
assert not re.search(r'\b(sorry|admit|unsafe|native_decide)\b',(D/'replay/Hurlbert.lean').read_text())
inputs={}
for line in (D/'inputs-before.sha256').read_text().splitlines():
 h,p=line.split('  ',1);assert sha(D/p)==h;inputs[p]=h
receipts={}
for p in sorted((D/'downloads').glob('*/receipt.json')):receipts[str(p.relative_to(D))]={'sha256':sha(p),'responses':json.loads(p.read_text())}
(D/'http-receipts-index.json').write_text(json.dumps(receipts,indent=2)+'\n')
r={
 'lane':'hurlbert-review-r1','mathdb_id':356266,'reviewed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'recommendation':'HOLD','root_acceptance':False,'credit':0,
 'gates':{
  'A':{'verdict':'QUALIFIED_PASS','finding':'2022 v1 and MathDB faithful; 1992 corroborates; thesis original not recovered','references':['downloads/source-v1/text.txt:776-803,828-837','../expanded-corpus-r234/sources/chung-1992.txt:218-363']},
  'B':{'verdict':'PASS','finding':'Own code verifies full cyclic S4 Euler ordering and strict cycle; S3 exhaustive; S4 extensive','evidence':'mathematics.json'},
  'C':{'verdict':'QUALIFIED_PASS','finding':'No full-Sn prior refutation located; material Albert-West 2009 restricted-class obstruction recovered; bounded title/body coverage only','critical_prior_art':{'authors':'Michael Albert and Julian West','title':'Universal cycles for permutation classes','year':2009,'doi':'10.46298/dmtcs.2727','location':'downloads/permutation-classes/text.txt:98-107','scope':'8-edge Av4(132,213), not full S4'},'limits':['Thesis body unrecovered','Jackson 1993 full body unread; only denied-host full text located','163 citing works title-screened, not all full texts read','Several recent k-permutation papers title-screened only','Unindexed or folklore prior art not excluded']},
  'D':{'verdict':'QUALIFIED_PASS','finding':'Substantive full-S4 refutation provisionally; no demonstrated routine augmentation, but new Albert-West comparison required','evidence':['printed-comparison.json','albert-west-augmentation.json']},
  'E':{'verdict':'FAIL','replay_pass':True,'literal_negation_present':False,'finding':'Endpoint is existential counterexample, not negation of all-n conjecture Prop','references':['replay/Hurlbert.lean:7-25','replay/Hurlbert.lean:36-54'],'missing_bridge':'Define all-n arbitrary-tour finite-alphabet conjecture Prop and specialize it at n=4 to contradict tour_not_realizable','estimated_cost':'6-15 Lean lines, new declaration audits, regenerated archive and fresh replay'}
 },
 'required_before_acceptance':['Fresh revised packet proving literal all-n negation, with strict replay and all-declaration axiom audit','Correct prior-art dossier and explicitly reconcile Albert-West printed restricted-class obstructions with short-augmentation exclusion'],
 'replay':{'lean_version':'4.34.1','mathlib_pin':'d13f23b723b8a846827a245b89c10fc7d3f11612','strict_build_exit_code':0,'inventory_exit_code':0,'axioms_exit_code':0,'leanchecker_exit_code':0,'leanchecker_module':'Hurlbert','local_declarations':13,'allowed_axioms':['propext','Classical.choice','Quot.sound'],'source_sha256':sha(D/'replay/Hurlbert.lean'),'trust_limit':'Supplied prebuilt dependency oleans trusted; no source-to-cache attestation'},
 'mathematics':json.loads((D/'mathematics.json').read_text()),
 'input_hashes_before':inputs,'input_hashes_after':inputs,'input_hashes_unchanged':True,
 'manifest_before_sha256':sha(D/'inputs-before.sha256'),'manifest_after_sha256':sha(D/'inputs-after.sha256'),
 'http_receipts':'http-receipts-index.json','review':'REVIEW.md',
 'constraints':{'write_scope':'hurlbert-review-r1 only','children':0,'git_calls':0,'discovery_scripts_executed':False,'python_isolated':True,'caps_driver':'scripts/capped.sh','lean_memory_flag':'-M3500','cpu_limit_s':120,'wall_limit_s':140,'rss_limit_GiB':6,'cpu_affinity_count':2,'MALLOC_ARENA_MAX':2,'no_background_jobs_left':True}
}
(D/'review.json').write_text(json.dumps(r,indent=2)+'\n')
print('Finalized review.json; input hashes and axiom audit verified.')
