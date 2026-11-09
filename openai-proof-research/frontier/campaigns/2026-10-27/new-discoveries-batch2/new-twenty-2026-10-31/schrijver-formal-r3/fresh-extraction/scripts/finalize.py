from pathlib import Path
import json,hashlib,re,collections
r=Path(__file__).resolve().parent.parent
replay=json.loads((r/'fresh-extraction/replay-result.json').read_text())
assert replay['status']=='PASS_PARTIAL_ONLY'
audit=(r/'fresh-extraction/logs/replay-build-Audit.log').read_text()
count=int(re.search(r'TOTAL_LOCAL_DECLARATIONS (\d+)',audit)[1])
before=json.loads((r/'outputs/frozen-before.json').read_text())
after={f:hashlib.sha256((r/'src'/f).read_bytes()).hexdigest() for f in before}
assert before==after
(r/'outputs/frozen-after.json').write_text(json.dumps(after,indent=2)+'\n')
manifest=json.loads((r/'outputs/input-manifest.json').read_text())
assert all(hashlib.sha256((r.parent/f).read_bytes()).hexdigest()==h for f,h in manifest.items())
modules={p.stem:dict(path=str(p.relative_to(r)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),strict_compiled=True,leanchecker=True) for p in (r/'src').glob('*.lean')}
result=dict(mathdb_id=352827,status='PARTIAL',unconditional_endpoint=False,conditional_endpoint='Schrijver.mathdb_352827_conditional',self_accepted=False,accepted_credit=0,root_decides=True,modules=modules,frozen_unchanged=True,frozen_hashes=after,inputs_unchanged=True,
audit=dict(total=count,by_module=dict(collections.Counter(re.findall(r'^MODULE (\S+)',audit,re.M))),unsafe=0,partial=0,unsafe_rec=0,implemented_by=0,extern=0,allowed_transitive_axioms=['propext','Classical.choice','Quot.sound'],log='fresh-extraction/logs/replay-build-Audit.log'),
remaining_props={'Schrijver.LowerCertificateBridge':'(SG 27 12).Connected ∧ ∃ a b, 8 ≤ (SG 27 12).dist a b','Schrijver.UpperCertificateBridge':'(SG 28 12).Connected ∧ ∀ a b, ∃ p : (SG 28 12).Walk a b, p.length ≤ 6'},
missing_bridges=['stored efficient enumeration equals proved complete reference enumeration','packed lookup correspondence and injectivity','concrete representative rotation coverage','literal connectivity and metric transfer'],
completed=['bounded bitmask bijection with both inverse laws','validMask completeness','literal rotation automorphisms and bit alignment','complete reference enumeration membership theorem','generic indexed-to-literal isomorphism under explicit coverage premises','packed parent and split-label checker soundness','all 116 upper representative trees kernel checked','819-vertex indexed connectivity and distance-8 pair'],
replay=dict(fresh=True,status=replay['status'],strict_serial=True,modules_checked=len(modules),negative_controls=replay['negative'],receipt='fresh-extraction/replay-result.json'),
computation=json.loads((r/'outputs/computation.json').read_text()),source_archive='schrijver-partial-source.zip',prior_art_status='Inherited qualified hold; no new novelty clearance',operational_exceptions=['initial read-only and lightweight orchestration calls were not capped','failed whole-array kernel checks exceeded Lean memory limit and were replaced with packed or split checks'])
(r/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status=result['status'],modules=len(modules),audit_total=count,frozen_unchanged=True)))
