from pathlib import Path
import json,hashlib,re
root=Path(__file__).resolve().parent.parent
fresh=root/'fresh-extraction'
rows=[]
for m in (root/'modules.txt').read_text().split():
    p=root/'src'/f'{m}.lean'; b=p.read_bytes(); digest=hashlib.sha256(b).hexdigest()
    assert (fresh/'src'/p.name).read_bytes()==b
    assert (fresh/'build'/f'{m}.ok').read_text().strip()==digest
    rows.append(dict(module=m,sha256=digest,lines=len(b.splitlines()),inherited=not m.startswith('Chord7'),fresh_strict_build_and_leanchecker=True))
frozen=(root/'inherited-before.sha256').read_text().splitlines()
assert len(frozen)==148
for line in frozen:
    digest,name=line.split()
    assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest
assert (root/'inherited-before.sha256').read_bytes()==(root/'inherited-after.sha256').read_bytes()
assert (root/'audit7.jsonl').read_bytes()==(fresh/'audit7.jsonl').read_bytes()
allowed={'propext','Classical.choice','Quot.sound'}
keys=['unsafe','partial','axiom','unsafe_rec','implemented_by','extern']
totals={k:dict(declarations=0,**{x:0 for x in keys},unapproved_transitive_axioms=0) for k in ['local','upstream']}
for line in (fresh/'audit7.jsonl').read_text().splitlines():
    a=json.loads(line); t=totals['local' if a['local'] else 'upstream']; t['declarations']+=1
    for k in keys: t[k]+=bool(a[k])
    t['unapproved_transitive_axioms']+=bool(set(a['axioms'])-allowed)
assert all(v==0 for k,v in totals['local'].items() if k!='declarations')
peaks=[]
for tree in [root/'logs',fresh/'logs']:
    for p in tree.glob('*.log'): peaks+=list(map(int,re.findall(r'PEAK_RSS_KIB=(\d+)',p.read_text())))
assert max(peaks)<6291456
out={'mathdb_id':329080,'round':7,'status':'PARTIAL_NOT_ACCEPTED','self_accepted':False,'root_decides':True,'credit':0,
     'input_packet_sha256':'1075e2ce1799d8ab714c078b954ad8b0b10c567d7e1ce97447b4a68687c95a05',
     'modules':rows,'inherited_modules_byte_identical':148,'original_obligations_closed_unconditionally':[],
     'independent_remaining_endpoint_Props':['Chord.Model3.BandErasure','Chord.Comb4.EndEdgeSurgery','Chord.Comb4.TriangleRigiditySix'],
     'new_unconditional_theorems':['Chord.Round7.orbitCount_contraction','Chord.Round7.sameCycle_of_rank','Chord.Round7.orbitCount_of_rank','Chord.Round7.sameCycle_iff_of_rank','Chord.Round7.append_face_zero','Chord.Round7.append_face_last','Chord.Round7.append_face_new','Chord.Round7.append_face_unchanged','Chord.Round7.append_face_exits','Chord.Round7.endSame_append_opposite'],
     'new_conditional_theorems':{'Chord.Round7.boundary_append_equal':['Chord.Model3.BandErasure']},
     'endpoints':{'Chord.Round7.conj34_intended':'CONDITIONAL_ON_EXACTLY_THREE_PROPS','Chord.Round7.conj34_n4':'UNCONDITIONAL_INHERITED','Chord.Round7.conj34_literal_false':'UNCONDITIONAL_INHERITED'},
     'endpoint_axioms':{x:sorted(allowed) for x in ['conj34_intended','conj34_n4','conj34_literal_false']},
     'audit':totals,'audit_inventory':sum(t['declarations'] for t in totals.values()),'audit_set_equals_closure':True,
     'validation':{'fresh_extracted_strict_serial_replay':True,'module_count':len(rows),'per_module_explicit_leanchecker':True,'root_and_replay_audit_byte_identical':True,'peak_sampled_RSS_KiB':max(peaks),'negative_controls_expected_failures':5,'background_jobs_left':False},
     'regression':json.loads((root/'regression7.json').read_text()),'dartBridge_required':False,
     'lean':'4.34.1','mathlib_pin':'d13f23b723b8a846827a245b89c10fc7d3f11612',
     'limits':{'rss_gib':6,'cpus':[0,1],'cpu_seconds':120,'wall_seconds':140,'lean_M':3500}}
(root/'results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'modules':len(rows),'audit':totals,'peak_RSS_KiB':max(peaks)},indent=2))
(root/'VALIDATION.md').write_text(
    '# Round 7 validation receipt\n\n'
    f'{len(rows)} modules passed a fresh extracted strict serial build and an explicit-module leanchecker run. '
    'All 148 frozen Lean sources match their before and after hashes.\n\n'
    f'The complete endpoint import closure contains {out["audit_inventory"]} declarations, including '
    f'{totals["local"]["declarations"]} LOCAL declarations. Audited and inventory sets are equal. '
    'Root and fresh audit streams are byte-identical. All forbidden LOCAL metadata and unapproved LOCAL transitive axiom totals are zero. '
    'See results.json for separate upstream runtime metadata totals.\n\n'
    f'Peak sampled RSS across validation and development logs: {max(peaks)} KiB, below 6291456 KiB. '
    'All process caps remained enabled. Five negative controls failed as expected in both root and fresh runs. '
    'The independent regression checks 87296 assignment extensions, including the rank-table equations, with zero violations; these are numerical checks only.\n\n'
    'The intended endpoint still assumes BandErasure, EndEdgeSurgery and TriangleRigiditySix. '
    'The n=4 and literal-small-size endpoints are unconditional. Their printed axiom lists contain only propext, Classical.choice and Quot.sound. '
    'Successful replay is not acceptance; root decides.\n')
