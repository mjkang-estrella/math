from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parent.parent
F=R/'fresh-extraction'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old={line.split()[1]:line.split()[0] for line in (R/'hashes/inherited-before.sha256').read_text().splitlines()}
assert len(old)==110
assert all(sha(R/p)==h for p,h in old.items())
(R/'hashes/inherited-after.sha256').write_text(''.join(f'{sha(R/p)}  {p}\n' for p in sorted(old)))
assert (R/'hashes/inherited-before.sha256').read_text()==(R/'hashes/inherited-after.sha256').read_text()
mods=(R/'modules.txt').read_text().splitlines()
assert len(mods)==len(set(mods))==117
rows=[]
for m in mods:
    p=R/'src'/f'{m}.lean'; q=F/'src'/f'{m}.lean'
    assert sha(p)==sha(q)
    assert (F/'build'/f'{m}.ok').read_text().strip()==sha(p)
    rows.append(dict(module=m,sha256=sha(p),lines=len(p.read_text().splitlines()),inherited=f'src/{m}.lean' in old,fresh_replay=True,leanchecker=True))
audit=[json.loads(x) for x in (F/'audit.jsonl').read_text().splitlines()]
fields=['unsafe','partial','axiom','unsafe_rec','implemented_by','extern']
allowed={'propext','Classical.choice','Quot.sound'}
totals={}
for label,local in [('local',True),('upstream',False)]:
    ar=[x for x in audit if x['local']==local]
    totals[label]={'declarations':len(ar),**{k:sum(x[k] for x in ar) for k in fields},'unapproved_transitive_axioms':sum(not set(x['axioms'])<=allowed for x in ar)}
assert not any(v for k,v in totals['local'].items() if k!='declarations')
logs=list((R/'logs').glob('*.log'))+list((F/'logs').glob('*.log'))
peak=max([int(x) for p in logs for x in re.findall(r'PEAK_RSS_KIB=(\d+)',p.read_text())])
# Final audit is a build module; its inventory excludes the audit implementation itself.
assert any(f'inventory={len(audit)} audited={len(audit)}' in p.read_text() for p in (F/'logs').glob('*.log'))
results=dict(mathdb_id=329080,round='4B',status='PARTIAL_NOT_ACCEPTED',self_accepted=False,root_decides=True,credit=0,
 frozen_archive_sha256='160d9b3f87f5e54b5fc0e3af79abe8ff5c2189afbf28aec21140025ddc750208',frozen_110_byte_identical=True,
 closed_Props=[],remaining_original_Props=['RepresentativeStep','RepresentativeExistence','BipartitePlanarity','TriangleReduction','TriangleRigidityLarge'],
 new_unproved_obligations=['EndEdgeSurgery','MonochromaticSplit','OddCycleWindow','TriangleRigiditySix'],
 partial_targets={'RepresentativeExistence':'actual end-face base invariant; general existence conditional on unproved surgery',
 'BipartitePlanarity':'innermost monochromatic selection proved; boundary induction conditional on unproved refined split',
 'TriangleReduction':'arbitrary five-chord compression and five-path obstruction proved; odd-cycle window unproved',
 'TriangleRigidityLarge':'n=5 proved from stated FiveProperty hypothesis; n>=6 remains'},
 conditional_hypotheses={'Chord.Comb4.conj34_intended':['RepresentativeStep','Heredity','TriangleReduction','TriangleRigiditySix'],
 'Chord.Comb4.conj34_intended_surgery':['EndEdgeSurgery','MonochromaticSplit','OddCycleWindow','Heredity','TriangleRigiditySix'],
 'Chord.Comb4.conj34_n4':[],'Chord.Comb4.conj34_literal_false':[]},
 model_Props_not_claimed=['DartBridge','OrbitCounterCorrect','FacePermutationCorrect','EulerRealization','Deletion','Heredity'],
 audit=totals,audit_inventory=len(audit),audit_set_equals_closure=True,modules=rows,
 regression=json.loads((R/'regression.json').read_text()),sanity_regression=json.loads((R/'sanity-regression.json').read_text()),
 validation=dict(fresh_extracted_serial_rebuild=True,per_module_leanchecker=True,modules_checked=len(mods),peak_sampled_RSS_KiB=peak,
 resource_caps=dict(rss_GiB=6,cpus=[0,1],cpu_seconds=120,wall_seconds=140,lean_M=3500),background_jobs_left=False),
 lean='4.34.1',mathlib_pin='d13f23b723b8a846827a245b89c10fc7d3f11612')
(R/'results.json').write_text(json.dumps(results,indent=2)+'\n')
(R/'VALIDATION.md').write_text(f'''# Validation receipts

PARTIAL, NOT ACCEPTED. No original target Prop closed.

All {len(mods)} modules (110 inherited, 7 new including the audit) rebuilt from a fresh source-only extraction and passed leanchecker with explicit module arguments. All 110 inherited SHA-256 hashes are unchanged. The final import-closure audit inventories and audits exactly {len(audit)} declarations, with both set inclusions checked in Lean. LOCAL metadata: {json.dumps(totals['local'])}. Upstream metadata: {json.dumps(totals['upstream'])}. Upstream runtime metadata is reported separately and is not attributed to LOCAL proofs. All LOCAL transitive axioms are in the three permitted names.

Peak sampled summed session RSS: {peak} KiB. Strict serial calls use the required CPU, wall, affinity, RSS and allocator limits. Full uniquely named call logs are retained under logs/ and fresh-extraction/logs/. Fresh replay progress is in logs/fresh-replay.log. No background job remains after handback.

Independent representative-state regression checks every assignment at n=3 through 7 and every two-end extension at n=3 through 6: no violations. The inherited independent small-table regression checks all labelled matchings and side assignments through n=5 and reproduces range-{{1,2}} class counts 0,0,1,4,1. Negative controls reject the wrong Euler offset, omission of the empty circle, uniqueness at n=4 and the adjacent-pair representative. These computations do not discharge a general Prop.
''')
print(json.dumps(dict(modules=len(mods),inherited_unchanged=len(old),audit=totals,peak_RSS_KiB=peak)))
