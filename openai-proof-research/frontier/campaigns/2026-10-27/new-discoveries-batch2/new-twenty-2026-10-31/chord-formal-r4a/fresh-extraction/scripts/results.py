import json,pathlib,hashlib,re
root=pathlib.Path.cwd();fresh=root/'fresh-extraction'
mods=(root/'modules.txt').read_text().splitlines()
base=(root/'frozen/modules.txt').read_text().splitlines()
rows=[]
for m in mods:
    p=root/'src'/f'{m}.lean';data=p.read_bytes();digest=hashlib.sha256(data).hexdigest()
    assert data==(fresh/'src'/p.name).read_bytes()
    if m in base: assert data==(root/'frozen/packet/src'/p.name).read_bytes()
    assert (fresh/'build'/f'{m}.ok').read_text().strip()==digest
    rows.append(dict(module=m,sha256=digest,lines=len(data.splitlines()),inherited=m in base,fresh_strict_build_and_leanchecker='PASS'))
assert (root/'frozen-before.sha256').read_bytes()==(root/'frozen-after.sha256').read_bytes()
keys=['declarations','unsafe','partial','axiom','unsafe_rec','implemented_by','extern','unapproved_transitive_axioms']
counts={k:dict.fromkeys(keys,0) for k in ['local','upstream']}
for line in (fresh/'audit.jsonl').open():
    r=json.loads(line);c=counts['local' if r['local'] else 'upstream'];c['declarations']+=1
    for k in keys[1:-1]: c[k]+=bool(r[k])
    c['unapproved_transitive_axioms']+=bool(set(r['axioms'])-{'propext','Classical.choice','Quot.sound'})
assert all(v==0 for k,v in counts['local'].items() if k!='declarations')
match=re.search(r'CLOSURE inventory=(\d+) audited=(\d+) LOCAL=(\d+); sets equal',(fresh/'logs/audit-build.log').read_text())
assert match and match[1]==match[2]
res=dict(mathdb_id=329080,round='4A',status='PARTIAL_NOT_ACCEPTED',self_accepted=False,root_decides=True,credit=0,
lean='4.34.1',dependency_pin='d13f23b723b8a846827a245b89c10fc7d3f11612',
frozen_archive_sha256='76d35a8b86707ff534088ba93e877c7a05c221b3c0010d889bec958562371e5f',
archive_sha256=hashlib.sha256((root/'chord-source.zip').read_bytes()).hexdigest(),inherited_modules_byte_identical=True,inherited_modules=len(base),modules=rows,
new_closed_Props=['Chord.Model3.SwapCycleLaw'],remaining_surgery_Props=['Chord.Model3.BandErasure'],
requested_targets=dict(SwapCycleLaw='PROVED',BandErasure='OPEN',Deletion='OPEN',EulerRealization='CONDITIONAL_ON_BAND_ERASURE',Heredity='CONDITIONAL_ON_BAND_ERASURE'),
conditional_hypotheses=dict(conj34_intended_model4=['BandErasure','RepresentativeExistence','FiveChordLemma','TriangleReduction','TriangleRigidity'],conj34_n4_model4=['FourChordEnumeration']),
audit=counts,validation=dict(fresh_extracted_serial_rebuild='PASS',formal_modules=len(mods),individual_leanchecker='PASS',audit_inventory=int(match[1]),audit_audited=int(match[2]),audit_sets_equal=True,audit_tool='ChordModel4Audit',source_extraction_equality=True),
regression=json.loads((root/'regression.json').read_text()),limits=dict(rss_gib=6,cpus=[0,1],cpu_seconds=120,wall_seconds=140,lean_memory_mb=3500,malloc_arena_max=2),
limitations=['No general BandErasure proof.','No deletion_proved theorem.','EulerRealization and Heredity are conditional.','No combinatorial Props work.','Final endpoint still has model and combinatorial hypotheses.','DartBridge remains open.'])
(root/'results.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps(dict(audit=counts,validation=res['validation'],archive_sha256=res['archive_sha256'])))
