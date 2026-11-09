import json,pathlib,hashlib,re
root=pathlib.Path.cwd()
fresh=root/'fresh-extraction'
modules=(root/'modules.txt').read_text().splitlines()
base=(root/'frozen/modules.txt').read_text().splitlines()
rows=[]
for m in modules:
    p=root/'src'/f'{m}.lean'
    data=p.read_bytes()
    assert data==(fresh/'src'/p.name).read_bytes()
    if m in base: assert data==(root/'frozen/src'/p.name).read_bytes()
    assert (fresh/'build'/f'{m}.ok').read_text().strip()==hashlib.sha256(data).hexdigest()
    rows.append({'module':m,'sha256':hashlib.sha256(data).hexdigest(),'lines':len(data.splitlines()),'inherited':m in base,'fresh_strict_build_and_leanchecker':'PASS'})
counts={k:dict(declarations=0,unsafe=0,partial=0,axiom=0,unsafe_rec=0,implemented_by=0,extern=0,unapproved_transitive_axioms=0) for k in ('local','upstream')}
allowed={'propext','Classical.choice','Quot.sound'}
for line in (fresh/'audit.jsonl').open():
    x=json.loads(line); c=counts['local' if x['local'] else 'upstream']; c['declarations']+=1
    for k in ('unsafe','partial','axiom','unsafe_rec','implemented_by','extern'): c[k]+=bool(x[k])
    c['unapproved_transitive_axioms']+=bool(set(x['axioms'])-allowed)
assert all(v==0 for k,v in counts['local'].items() if k!='declarations')
log=(fresh/'logs/audit-build.log').read_text()
match=re.search(r'CLOSURE inventory=(\d+) audited=(\d+) LOCAL=(\d+); sets equal',log)
assert match and match[1]==match[2]
res={'mathdb_id':329080,'round':'3A','status':'PARTIAL_NOT_ACCEPTED','self_accepted':False,'root_decides':True,'credit':0,
'lean':'4.34.1','dependency_pin':'d13f23b723b8a846827a245b89c10fc7d3f11612',
'frozen_archive_sha256':'ecf5383aea8e309460520702f6bbbf87d6d85b774fddd36debd2434bfd7f80fa',
'archive_sha256':hashlib.sha256((root/'chord-source.zip').read_bytes()).hexdigest(),
'inherited_modules_byte_identical':True,'inherited_modules':len(base),'modules':rows,
'new_closed_Props':[],'inherited_closed_Props':['OrbitCounterCorrect','FacePermutationCorrect'],
'requested_targets':{'Deletion':'OPEN','EulerRealization':'CONDITIONAL_ON_DELETION','Heredity':'CONDITIONAL_ON_DELETION','DartBridge':'OPEN_OPTIONAL'},
'new_remaining_surgery_Props':['Chord.Model3.SwapCycleLaw','Chord.Model3.BandErasure'],
'conditional_hypotheses':{'conj34_intended_model3':['Deletion','RepresentativeExistence','FiveChordLemma','TriangleReduction','TriangleRigidity'],'conj34_n4_model3':['FourChordEnumeration']},
'audit':counts,'validation':{'fresh_extracted_serial_rebuild':'PASS','formal_modules':len(modules),'individual_leanchecker':'PASS','audit_inventory':int(match[1]),'audit_audited':int(match[2]),'audit_sets_equal':True,'audit_tool':'ChordModel3Audit','source_extraction_equality':True},
'regression':json.loads((root/'regression.json').read_text()),
'limits':{'rss_gib':6,'cpus':[0,1],'cpu_seconds':120,'wall_seconds':140,'lean_memory_mb':3500,'malloc_arena_max':2},
'limitations':['No deletion_proved theorem.','No previously open full model Prop closed.','No combinatorial Props work.','Band-erasure regression is not a proof.']}
(root/'results.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps({'audit':counts,'validation':res['validation'],'archive_sha256':res['archive_sha256']}))
