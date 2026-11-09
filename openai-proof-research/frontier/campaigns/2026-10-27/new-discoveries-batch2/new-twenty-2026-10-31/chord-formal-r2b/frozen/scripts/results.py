import pathlib,json,hashlib
root=pathlib.Path.cwd()
mods=[]
for p in sorted(root.glob('Chord*.lean')):
    if p.name=='ChordAudit.lean':continue
    mods.append({'file':p.name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'lines':len(p.read_text().splitlines()),'olean':((root/'build'/p.with_suffix('.olean').name).exists() or (root/'fresh-extraction/build'/p.with_suffix('.olean').name).exists())})
audit=root/'fresh-extraction/audit.jsonl'
if not audit.exists():audit=root/'audit.jsonl'
tot={'local':{},'upstream':{}}
if audit.exists():
    for line in audit.open():
        d=json.loads(line);s=tot['local' if d['local'] else 'upstream']
        s['declarations']=s.get('declarations',0)+1
        for key in ['unsafe','partial','axiom','unsafe_rec','implemented_by','extern']:
            s[key]=s.get(key,0)+int(d[key])
        s['unapproved_transitive_axioms']=s.get('unapproved_transitive_axioms',0)+len(set(d['axioms'])-{'propext','Classical.choice','Quot.sound'})
res={'mathdb_id':329080,'status':'PARTIAL_NOT_ACCEPTED','self_accepted':False,'root_decides':True,'credit':0,'modules':mods,
     'endpoints':{'conj34_intended':'CONDITIONAL','conj34_n4':'CONDITIONAL_ON_EXACT_ENUMERATION_TARGET','conj34_literal_false':'UNCONDITIONAL','printed_conjecture_false':'UNCONDITIONAL','genusRange_r3':'UNCONDITIONAL'},
     'remaining_Props':['DartBridge','OrbitCounterCorrect','FacePermutationCorrect','EulerRealization','Deletion','Heredity','BipartitePlanarity','FiveChordLemma','TriangleReduction','TriangleRigidity','RepresentativeExistence','FourChordEnumeration'],
     'audit':tot,'regression':json.loads((root/'regression.json').read_text()),
     'dependency_pin':'d13f23b723b8a846827a245b89c10fc7d3f11612','lean':'4.34.1',
     'limits':{'rss_gib':6,'cpus':[0,1],'cpu_seconds':120,'wall_seconds':140,'lean_memory_mb':3500},
     'limitations':['Generic face-orbit counter correctness and two-dart bridge unproved.','No unconditional intended uniqueness or n4 completeness theorem.','Word/involution correspondence unproved.','Finite Python counts are not Lean class-count proofs.']}
(root/'results.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps({'modules':len(mods),'audit':tot,'status':res['status']}))
res['archive_sha256']=hashlib.sha256((root/'chord-source.zip').read_bytes()).hexdigest()
res['replay_modules']=[{'module':m,'marker_matches_source':((root/'fresh-extraction/build'/f'{m}.ok').read_text().strip()==hashlib.sha256((root/f'{m}.lean').read_bytes()).hexdigest()) if (root/'fresh-extraction/build'/f'{m}.ok').exists() else False} for m in (root/'modules.txt').read_text().split()]
res['conditional_hypotheses']={'conj34_intended':['RepresentativeExistence','Heredity','FiveChordLemma','TriangleReduction','TriangleRigidity'],'conj34_n4':['FourChordEnumeration']}
(root/'results.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps({'all_replay_markers_match':all(m['marker_matches_source'] for m in res['replay_modules']),'archive_sha256':res['archive_sha256']}))
