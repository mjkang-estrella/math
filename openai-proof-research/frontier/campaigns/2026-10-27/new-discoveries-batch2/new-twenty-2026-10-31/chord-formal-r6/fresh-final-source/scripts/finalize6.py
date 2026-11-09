import pathlib,json,hashlib,re
root=pathlib.Path(__file__).resolve().parent.parent
modules=(root/'modules.txt').read_text().split()
rows=[]
for m in modules:
    p=root/'src'/f'{m}.lean'; b=p.read_bytes()
    rows.append({'module':m,'sha256':hashlib.sha256(b).hexdigest(),'lines':len(b.splitlines()),'inherited':not m.startswith('Chord6')})
assert sum(x['inherited'] for x in rows)==144
frozen={line.split()[1]:line.split()[0] for line in (root/'inherited-before.sha256').read_text().splitlines()}
assert len(frozen)==144
for name,digest in frozen.items(): assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest
fresh=root/'fresh-extraction'
for row in rows:
    m=row['module']
    assert (fresh/'build'/f'{m}.ok').read_text().strip()==row['sha256']
    assert (fresh/'src'/f'{m}.lean').read_bytes()==(root/'src'/f'{m}.lean').read_bytes()
    row['fresh_strict_build_and_leanchecker']=True
assert (root/'audit6.jsonl').read_bytes()==(fresh/'audit6.jsonl').read_bytes()
allowed={'propext','Classical.choice','Quot.sound'}
totals={k:dict(declarations=0,unsafe=0,partial=0,axiom=0,unsafe_rec=0,implemented_by=0,extern=0,unapproved_transitive_axioms=0) for k in ('local','upstream')}
for line in (fresh/'audit6.jsonl').read_text().splitlines():
    a=json.loads(line); t=totals['local' if a['local'] else 'upstream']; t['declarations']+=1
    for k in ('unsafe','partial','axiom','unsafe_rec','implemented_by','extern'): t[k]+=bool(a[k])
    t['unapproved_transitive_axioms']+=bool(set(a['axioms'])-allowed)
assert all(v==0 for k,v in totals['local'].items() if k!='declarations')
peaks=[]
for tree in (root/'logs',fresh/'logs'):
    for p in tree.glob('*.log'):
        peaks.extend(map(int,re.findall(r'PEAK_RSS_KIB=(\d+)',p.read_text())))
assert max(peaks)<6291456
result={
'mathdb_id':329080,'round':6,'status':'PARTIAL_NOT_ACCEPTED','self_accepted':False,'root_decides':True,'credit':0,
'input_packet_sha256':'6be45630fee1ea460e8c66b5ae23a831bcc41ba85108afbb1f38f396dc9dd1ec',
'modules':rows,'inherited_modules_byte_identical':144,
'original_obligations_closed_unconditionally':[],
'original_obligations_still_without_unconditional_proof':['Chord.Model3.BandErasure','Chord.Comb4.EndEdgeSurgery','Chord.Comb4.MonochromaticSplit','Chord.Comb4.TriangleRigiditySix'],
'independent_remaining_endpoint_Props':['Chord.Model3.BandErasure','Chord.Comb4.EndEdgeSurgery','Chord.Comb4.TriangleRigiditySix'],
'new_conditional_reduction':'Chord.Round6.monochromaticSplit_of_bandErasure : BandErasure → MonochromaticSplit',
'new_unconditional_theorems':['Chord.Round6.sameCycle_removeNone','Chord.Round6.swap_orbitCount_refined','Chord.Round6.swap_split_iff','Chord.Round6.swap_sameCycle_iff','Chord.Round6.innermost_distinct'],
'dartBridge_required':False,
'endpoints':{'Chord.Round6.conj34_intended':'CONDITIONAL_ON_EXACTLY_THREE_INDEPENDENT_PROPS','Chord.Round6.conj34_n4':'UNCONDITIONAL_INHERITED','Chord.Round6.conj34_literal_false':'UNCONDITIONAL_INHERITED'},
'endpoint_axioms':{x:sorted(allowed) for x in ('conj34_intended','conj34_n4','conj34_literal_false')},
'audit':totals,'audit_inventory':sum(t['declarations'] for t in totals.values()),'audit_set_equals_closure':True,
'validation':{'fresh_extracted_strict_serial_replay':True,'module_count':len(rows),'per_module_explicit_leanchecker':True,'root_and_replay_audit_byte_identical':True,'peak_sampled_RSS_KiB':max(peaks),'negative_controls_expected_failures':5,'background_jobs_left':False},
'regression':json.loads((root/'regression6.json').read_text()),
'lean':'4.34.1','mathlib_pin':'d13f23b723b8a846827a245b89c10fc7d3f11612',
'limits':{'rss_gib':6,'cpus':[0,1],'cpu_seconds':120,'wall_seconds':140,'lean_M':3500}}
(root/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'modules':len(rows),'audit':totals,'peak_RSS_KiB':max(peaks)},indent=2))
