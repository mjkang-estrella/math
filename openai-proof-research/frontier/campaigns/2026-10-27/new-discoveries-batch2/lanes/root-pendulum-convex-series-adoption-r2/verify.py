from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;S=P.parent/'sol-pendulum-convex-series-formal-r2'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
for r in json.loads((P/'review-freeze.json').read_text())['files']:
 p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
r=json.loads((P/'extracted/replay-receipt.json').read_text());assert r['status']=='MANDATORY_COMPONENT_SOURCE_ONLY_REPLAY_PASS' and r['declaration_count']==96 and not r['source_claim_pass']
assert r['initial_own_prebuilt_artifacts']==0 and r['archive_sha256']==sha(S/'component-source.zip')
for d in r['declarations']:
 assert set(d['axioms'])<={'propext','Classical.choice','Quot.sound'}
 assert not any(d[k] for k in ['unsafe','partial','axiom'])
assert {d['origin'] for d in r['declarations']}=={'Defs','Substitution','Moments','Source','Convexity','Series'}
assert r['declarations']==json.loads((S/'actual-declarations.json').read_text())
pins=json.loads((P/'extracted/pins-and-inputs.json').read_text());assert pins['pins_verified']==9 and pins['frozen_entries_verified']==532 and pins['originals_and_copies_unchanged']
out={'status':'PASS','root_fresh_source_only_replay':True,'mathematical_modules':6,'actual_declarations':96,'original_freeze_entries':532,'package_pins':9,'source_claim_pass':False,'credit':0}
(P/'verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
