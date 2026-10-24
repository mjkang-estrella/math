#!/usr/bin/env python3
"""Read-only proof-review intake; copied synthetic controls stay parent-local."""
from pathlib import Path
import base64,datetime,hashlib,json,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]
A=C/'fresh-structural-discovery-r210'; R=C/'structural-r210-proof-r1'; K=R/'packet'
read=lambda p:json.loads(p.read_bytes()); sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'c1a33524049f6b2575a52beb3b1ab0a30b450271c2f1e23cccf76c17d28d5210','MANIFEST':'058cf02299a7a5bbf9e11ba150799746892ebd701d1bebafb964254853dd3063','REPORT':'df5ac1174a161d8175d7be686ac7fd9208e0bfbcd75c29eb834d0850966275a5'}
def observe(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        assert not p.is_symlink(); e={'type':'directory' if p.is_dir() else 'file','mode':format(stat.S_IMODE(p.stat().st_mode),'04o')}
        if p.is_file():b=p.read_bytes(); e.update(bytes=len(b),sha256=sha(b))
        out['.' if p==root else p.relative_to(root).as_posix()]=e
    return out
def run(verifier,root,a):
    args=['python3','-I','-B',str(verifier),'--packet',str(root/'packet'),'--manifest',str(root/'MANIFEST.json'),'--report',str(root/'REPORT.md')]
    for k in ['FINAL','MANIFEST','REPORT']:args.extend(['--'+k.lower()+'-sha256',a[k]])
    return subprocess.run(args,capture_output=True,text=True)
before=observe(R); author_before=observe(A); assert author_before==read(P/'observed-root.json')
assert sha((R/'verify_packet.py').read_bytes())=='213d11e967c7b0f951f096e073e111ff05ee57c3480bc628dabdbc0776e26401'
assert (R/'verify_packet.py').read_bytes()==(K/'artifact/verify_packet.py').read_bytes()
v=run(R/'verify_packet.py',R,anchors); assert v.returncode==0,(v.stdout,v.stderr)
av=run(A/'verify_packet.py',A,read(P/'replay.json')['anchors']); assert av.returncode==0,(av.stdout,av.stderr)
copies=read(K/'private/input-copies.json'); assert len(copies)==75
prefix=A.relative_to(PROJECT).as_posix()+'/'
for e in copies:
    assert e['source'].startswith(prefix); rel=e['source'][len(prefix):]; assert rel in author_before
    assert e['copy'].startswith('private/') and 'packet/'+e['copy'] in before
    b=(PROJECT/e['source']).read_bytes(); assert b==(K/e['copy']).read_bytes()
    assert len(b)==e['bytes'] and sha(b)==e['sha256'] and author_before[rel]['mode']==e['source_mode']
tb=(PROJECT/'sources/preprints-tree.json').read_bytes(); assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree={e['path']:e for e in json.loads(tb)['tree']}; sources=read(K/'private/source-authentication.json'); assert sources['complete_tree_sha256']==sha(tb)
folder='preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/'
for e in sources['verified_blobs']:
    b=(K/'private/inputs/source334'/e['path']).read_bytes(); t=tree[folder+e['path']]
    assert len(b)==e['bytes']==t['size'] and sha(b)==e['sha256']
    assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==t['sha']
assert len(sources['verified_blobs'])==12
for name,copy in [('334-pinned-metadata.json','334.md'),('comparator-pinned-metadata.json','IsometricImmersion.lean')]:
    e=read(K/'private'/name); b=(K/'private/inputs'/copy).read_bytes()
    assert e['encoding']=='base64' and base64.b64decode(e['content'])==b and len(b)==e['size']
    assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['sha']
comparisons=read(K/'private/comparator-history-authentication.json'); histories=0
for e in comparisons:
    if 'original_path' not in e:continue
    assert e['original_path']=='frontier/campaigns/2026-10-14/fresh-structural-discovery-r22/candidate.md' and (e['start'],e['end']) in [(1520,3282),(3282,4123),(4123,6482)]
    with (PROJECT/e['original_path']).open('rb') as f:f.seek(e['start']); b=f.read(e['end']-e['start'])
    assert sha(b)==e['sha256'] and b==(K/f"private/inputs/history-r22-{e['start']}-{e['end']}.txt").read_bytes(); histories+=1
reading=read(K/'private/reading-extents.json'); extents=visual=0
for e in reading:
    p=K/'private/inputs'/e['input']; assert p.relative_to(R).as_posix() in before
    if 'extent' in e:
        assert e['extent']==[0,p.stat().st_size]; extents+=1
    else:
        for page in e['visual_pdf_pages_read']:
            name=f'nm86-p{page}.png' if p.name=='nakamura_maeda1986.pdf' else f'khuri2007-p{page}.png'
            f=K/'private/inputs/primary'/name; assert f.relative_to(R).as_posix() in before; visual+=1
controls=[]
with tempfile.TemporaryDirectory(prefix='proof-controls-',dir=P) as tmp:
    base=R/'synthetic-controls'; ca={'FINAL':sha((base/'packet/FINAL.md').read_bytes()),'MANIFEST':sha((base/'MANIFEST.json').read_bytes()),'REPORT':sha((base/'REPORT.md').read_bytes())}
    for case in ['intact','wrong-anchor','changed-bytes','extra-file','missing-file','file-mode','directory-mode']:
        dst=Path(tmp)/case; shutil.copytree(base,dst); aa=dict(ca); f=dst/'packet/private/sample.txt'
        if case=='wrong-anchor':aa['FINAL']='0'*64
        elif case=='changed-bytes':b=f.read_bytes(); f.write_bytes(bytes([b[0]^1])+b[1:])
        elif case=='extra-file':(dst/'packet/extra.txt').write_text('extra\n')
        elif case=='missing-file':f.unlink()
        elif case=='file-mode':f.chmod(stat.S_IMODE(f.stat().st_mode)^0o100)
        elif case=='directory-mode':(dst/'packet').chmod(stat.S_IMODE((dst/'packet').stat().st_mode)^0o020)
        q=run(R/'verify_packet.py',dst,aa); accepted=q.returncode==0; assert accepted==(case=='intact'),(case,q.stdout,q.stderr)
        controls.append({'case':case,'accepted':accepted,'expected':case=='intact'})
assert observe(R)==before and observe(A)==author_before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':json.loads(v.stdout),'author_verification':json.loads(av.stdout),'review_files':sum(e['type']=='file' for e in before.values()),'review_directories':sum(e['type']=='directory' for e in before.values()),'author_files_unchanged':sum(e['type']=='file' for e in author_before.values()),'review_originals_unchanged':True,'retained_input_bindings':len(copies),'canonical_blob_bindings':12,'formal_metadata_bindings':2,'original_history_spans':histories,'reading_extent_metadata_bindings':extents,'visual_record_identity_bindings':visual,'copied_controls':controls,'limits':'Parent read full REVIEW, FINAL, REPORT, READ-LIMITS, working deductions and verifier/control code. Underlying source, primary, history, comparator bodies and renders were identity-bound only. Reviewer semantic/visual coverage remains attributed; no inherited reading, new parent primary retrieval, formal endpoint coverage or contribution verdict.'}
for name,value in [('proof-replay.json',out),('proof-observed-root.json',before)]:
    p=P/name; p.write_text(json.dumps(value,indent=2)+'\n'); p.chmod(0o600)
print(json.dumps(out,indent=2))
