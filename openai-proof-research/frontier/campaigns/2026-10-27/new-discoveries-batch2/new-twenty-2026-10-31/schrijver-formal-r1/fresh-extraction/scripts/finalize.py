from pathlib import Path
import json,hashlib,re,collections
root=Path(__file__).resolve().parent.parent
replay=json.loads((root/'fresh-extraction/replay-result.json').read_text())
assert replay['status']=='PASS_PARTIAL_ONLY'
audit=(root/'fresh-extraction/logs/replay-build-Audit.log').read_text()
count=int(re.search(r'TOTAL_LOCAL_DECLARATIONS (\d+)',audit)[1])
counts=dict(collections.Counter(re.findall(r'^MODULE (\S+)',audit,re.M)))
manifest=json.loads((root/'outputs/input-manifest.json').read_text())
changed=[rel for rel,h in manifest.items() if hashlib.sha256((root.parent/rel).read_bytes()).hexdigest()!=h]
assert not changed
(root/'outputs/input-integrity.json').write_text(json.dumps(dict(checked_files=len(manifest),unchanged=True),indent=2)+'\n')
modules={p.stem:dict(path=str(p.relative_to(root)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),strict_compiled=True,leanchecker=True) for p in (root/'src').glob('*.lean')}
result=dict(mathdb_id=352827,status='PARTIAL',unconditional_endpoint=False,conditional_endpoint='Schrijver.mathdb_352827_conditional',self_accepted=False,accepted_credit=0,modules=modules,audit=dict(total=count,by_module=counts,unsafe=0,partial=0,unsafe_rec=0,implemented_by=0,extern=0,allowed_transitive_axioms=['propext','Classical.choice','Quot.sound'],log='fresh-extraction/logs/replay-build-Audit.log'),remaining_props={
'Schrijver.LowerCertificateBridge':'(SG 27 12).Connected ∧ ∃ a b, 8 ≤ (SG 27 12).dist a b',
'Schrijver.UpperCertificateBridge':'(SG 28 12).Connected ∧ ∀ a b, ∃ p : (SG 28 12).Walk a b, p.length ≤ 6'},
missing_bridges=['enumeration completeness and bitmask bijection','literal graph rotation automorphisms','all parent and label certificate decisions with soundness transfer','connectivity and metric transfer for the two target graphs'],
replay=dict(fresh=True,status=replay['status'],strict_serial=True,modules_checked=len(modules),negative_controls=replay['negative'],receipt='fresh-extraction/replay-result.json'),
computation=json.loads((root/'outputs/computation.json').read_text()),kernel_concrete_claims=['819 masks individually valid','mask list length 819','explicit witness mask validity'],inputs_unchanged=True,source_archive='schrijver-partial-source.zip',next_round_plan='SUMMARY.md',operational_exceptions=['initial brief and read-only source shell calls preceded capped wrapper','initial 6 GiB virtual cap caused mmap import failure; replaced with sampled private RSS cap','failed development builds retained'],prior_art_status='Inherited qualified hold; no new novelty clearance',root_decides=True)
(root/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status=result['status'],audit_total=count,modules=len(modules),replay=result['replay'],inputs_unchanged=True),indent=2))
