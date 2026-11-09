import pathlib, json, hashlib, collections
root=pathlib.Path.cwd()
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
modules=(root/'modules.txt').read_text().splitlines()
frozen=(root/'modules-r1.txt').read_text().splitlines()
entries=[]
for m in modules:
    p=root/'src'/f'{m}.lean'
    q=root/'fresh-extraction'/'src'/p.name
    assert p.read_bytes()==q.read_bytes()
    marker=root/'fresh-extraction'/'build'/f'{m}.ok'
    assert marker.read_text().strip()==sha(p)
    if m in frozen: assert p.read_bytes()==(root/'frozen'/p.name).read_bytes()
    entries.append({'module':m,'file':str(p.relative_to(root)),'sha256':sha(p),'lines':len(p.read_text().splitlines()),'inherited':m in frozen,'fresh_strict_build_and_leanchecker':'PASS'})
counts={'local':collections.Counter(),'upstream':collections.Counter()}
seen=set()
for line in (root/'fresh-extraction'/'audit.jsonl').open():
    row=json.loads(line)
    assert row['name'] not in seen
    seen.add(row['name'])
    d=counts['local' if row['local'] else 'upstream']
    d['declarations']+=1
    for k in ['unsafe','partial','axiom','unsafe_rec','implemented_by','extern']:
        d[k]+=int(row[k])
    bad=set(row['axioms'])-{'propext','Classical.choice','Quot.sound'}
    d['unapproved_transitive_axioms']+=bool(bad)
    if row['local']: assert not bad and not any(row[k] for k in ['unsafe','partial','axiom','unsafe_rec','implemented_by','extern'])
assert all('EXIT=0' in p.read_text() for p in (root/'fresh-extraction'/'logs').glob('*.log'))
reg=json.loads((root/'regression.json').read_text())
result={'mathdb_id':329080,'round':'2A','status':'PARTIAL_NOT_ACCEPTED','self_accepted':False,'root_decides':True,'credit':0,
'lean':'4.34.1','dependency_pin':'d13f23b723b8a846827a245b89c10fc7d3f11612',
'frozen_archive_sha256':'03971d4610581095feddea8040bd178f017d459794ac3e2374e73402d93ccbab',
'archive_sha256':sha(root/'chord-source.zip'),'inherited_modules_byte_identical':True,'modules':entries,
'closed_Props':['OrbitCounterCorrect','FacePermutationCorrect'],
'dependent_Props':{'EulerRealization':['Deletion'],'Heredity':['Deletion']},
'remaining_2A_independent_Props':['DartBridge','Deletion'],
'remaining_Props':['DartBridge','EulerRealization','Deletion','Heredity','BipartitePlanarity','FiveChordLemma','TriangleReduction','TriangleRigidity','RepresentativeExistence','FourChordEnumeration'],
'conditional_hypotheses':{'conj34_intended_model2':['Deletion','RepresentativeExistence','FiveChordLemma','TriangleReduction','TriangleRigidity'],'conj34_n4_model2':['FourChordEnumeration']},
'endpoints':{'conj34_intended_model2':'CONDITIONAL','conj34_n4_model2':'CONDITIONAL','conj34_literal_false_model2':'UNCONDITIONAL'},
'audit':{k:dict(v) for k,v in counts.items()},'regression':reg,
'validation':{'fresh_extracted_serial_rebuild':'PASS','formal_modules':len(modules),'individual_leanchecker':'PASS','audit_inventory':len(seen),'audit_audited':len(seen),'audit_sets_equal':True,'audit_tool':'ChordModel2Audit','source_extraction_equality':True},
'limits':{'rss_gib':6,'cpus':[0,1],'cpu_seconds':120,'wall_seconds':140,'lean_memory_mb':3500,'malloc_arena_max':2},
'limitations':['DartBridge and Deletion remain open.','EulerRealization and Heredity only proved conditional on Deletion.','No combinatorial Props work performed.','No unconditional intended uniqueness or n4 completeness endpoint.']}
(root/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'formal_modules':len(modules),'audit':result['audit'],'archive_sha256':result['archive_sha256']},indent=2))
