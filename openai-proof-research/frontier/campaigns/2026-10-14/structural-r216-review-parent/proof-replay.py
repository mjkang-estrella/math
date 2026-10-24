#!/usr/bin/env python3
"""Read-only proof-review artifact intake; no inherited semantic reading."""
from pathlib import Path
import datetime,hashlib,json,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2]
R=C/'structural-r216-proof-r1';K=R/'packet';A=C/'fresh-structural-discovery-r216'
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'f3b0803c3adb1d691bc97f8efcd78e2c2ce8a8d47ed9af8075dc710b39ff4b32','MANIFEST':'103fc921de1a1a6b44b89a838a7b616fa982586ddeb391a3babc852a78e81100','SELECTION':'fff6d1b51e7caa23e0097bd0444526f1413913c3d113e0f5cc0916120df4770c','REPORT':'6d65d44f5128459482fac836fa52ed259e3aa4824ed1cffa4c76685ee4542196'}
def observe(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        assert not p.is_symlink()
        e={'type':'directory' if p.is_dir() else 'file','mode':format(stat.S_IMODE(p.stat().st_mode),'04o')}
        if p.is_file():b=p.read_bytes();e.update(bytes=len(b),sha256=sha(b))
        out['.' if p==root else p.relative_to(root).as_posix()]=e
    return out
def run(root,a):
    args=['python3','-I','-B',str(R/'verify_packet.py'),'--packet',str(root/'packet')]
    for name in ['manifest','selection','report']:args.extend(['--'+name,str(root/(name.upper()+('.md' if name=='report' else '.json')))])
    for name in anchors:args.extend(['--'+name.lower()+'-sha',a[name]])
    return subprocess.run(args,capture_output=True,text=True)
before=observe(R);author_before=observe(A)
assert author_before==read(C/'discovery-structural-r216-parent/observed-root.json')
assert sha((R/'verify_packet.py').read_bytes())=='afd226a41356f13466b0e57e21cb5a04cd3b2757ff97349e51d416b9efc5a57e'
v=run(R,anchors);assert v.returncode==0,(v.stdout,v.stderr)
ab=read(K/'private/author-originals-before.json');aa=read(K/'private/author-originals-after.json')
assert aa['admitted_files_checked']==len(ab)==62 and aa['all_bytes_modes_unchanged'] and aa['after']==ab
for rel,e in ab.items():
    p=A/rel;assert p.is_relative_to(A);b=p.read_bytes()
    assert len(b)==e['bytes'] and sha(b)==e['sha256'] and stat.S_IMODE(p.stat().st_mode)==e['mode']
for n in ['STATEMENT.md','AUTHOR-PROOF.md']:assert (K/'private/inputs'/n).read_bytes()==(A/'packet'/n).read_bytes()
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree={e['path']:e for e in json.loads(tb)['tree']};source=read(K/'private/canonical-authentication.json')
prefix='preprints/A-counterexample-to-the-nearby-Lagrangian-conjecture-September-23-2026/'
assert len(source)==13 and {e['path'] for e in source}=={p for p,e in tree.items() if e['type']=='blob' and p.startswith(prefix)}
logs=[json.loads(s) for s in (K/'private/reads.jsonl').read_text().splitlines()]
text_count=0
for e in source:
    p=A/'packet/private/source340'/e['path'][len(prefix):];b=p.read_bytes();t=tree[e['path']]
    assert len(b)==e['bytes']==t['size'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==t['sha']
    if p.suffix=='.pdf':continue
    rel=p.relative_to(PROJECT).as_posix()
    intervals=sorted(x['bytes'] for x in logs if x.get('path')==rel and (x['kind'] in ['semantic','canonical README complete'] or x['kind'].startswith('bibliography /')))
    end=0
    for lo,hi in intervals:assert 0<=lo<=end and lo<=hi<=len(b);end=max(end,hi)
    assert end==len(b),(rel,intervals);text_count+=1
primary=0
for e in logs:
    if '/packet/private/primary/' not in e.get('path','') or not e['kind'].startswith('primary semantic'):continue
    p=PROJECT/e['path'];assert p.is_relative_to(A);b=p.read_bytes();lo,hi=e['bytes']
    assert 0<=lo<=hi<=len(b)==e['total'] and sha(b)==e['sha256'];primary+=1
controls=[]
with tempfile.TemporaryDirectory(prefix='proof-controls-',dir=P) as tmp:
    base=R/'tiny-controls';ca={key:sha((base/('packet/FINAL.md' if key=='FINAL' else key+('.md' if key=='REPORT' else '.json'))).read_bytes()) for key in anchors}
    for case in ['intact','wrong-anchor','changed-bytes','extra-file','missing-file','file-mode','directory-mode']:
        dst=Path(tmp)/case;shutil.copytree(base,dst);a=dict(ca);f=dst/'packet/payload.txt'
        if case=='wrong-anchor':a['FINAL']='0'*64
        elif case=='changed-bytes':b=f.read_bytes();f.write_bytes(bytes([b[0]^1])+b[1:])
        elif case=='extra-file':(dst/'packet/extra.txt').write_text('extra\n')
        elif case=='missing-file':f.unlink()
        elif case=='file-mode':f.chmod(0o644)
        elif case=='directory-mode':(dst/'packet').chmod(0o755)
        q=run(dst,a);ok=q.returncode==0;assert ok==(case=='intact'),(case,q.stdout,q.stderr)
        controls.append({'case':case,'accepted':ok,'expected':case=='intact'})
actual='feadd08d338035715987e81fdd1b142f82fe0a5db541b95d28385aed7d2fbc20'
wrong='feadd08d338035715987e81fdd1b142f82fe0a5db541b5b00e9afe4ec7d2fbc20'
assert sha((A/'verify_packet.py').read_bytes())==actual
assert actual in (C/'discovery-structural-r216-parent/replay.py').read_text()
for role in ['proof','contribution']:
    b=(C/'expanded-target-2026-10-17'/f'structural-r216-{role}-r1-brief.txt').read_text();assert wrong in b
assert observe(R)==before and observe(A)==author_before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':json.loads(v.stdout),'selected_subdirectories':2,'review_root_files':sum(e['type']=='file' for e in before.values()),'review_root_directories':sum(e['type']=='directory' for e in before.values()),'review_originals_bytes_modes_unchanged':True,'admitted_author_files_unchanged':62,'whole_author_root_unchanged_since_parent_intake':True,'canonical_blobs':13,'complete_text_read_record_bindings':text_count,'primary_semantic_extent_identity_bindings':primary,'original_history_bodies_read':0,'copied_controls':controls,'verifier_anchor_erratum':{'cause':'Parent transcription error in both dispatched review briefs; immutable initial briefs retained.','supplied':wrong,'actual':actual,'actual_matches_prior_parent_replay_and_committed_author_script':True,'four_author_packet_anchors_match':True},'formal_navigation':read(K/'private/formal-access.json'),'limits':'Parent read full REVIEW, FINAL, REPORT and READING-ACCESS. Source and primary read records identity-bound only, not inherited semantic reading. AIS truncation recovery, AACK font losses, unread intermediates, incidental editorial exposures and guarded-history limits retained. No contribution verdict or acceptance.'}
for name,value in [('proof-replay.json',out),('proof-observed-root.json',before)]:
    p=P/name;p.write_text(json.dumps(value,indent=2)+'\n');p.chmod(0o600)
print(json.dumps(out,indent=2))
