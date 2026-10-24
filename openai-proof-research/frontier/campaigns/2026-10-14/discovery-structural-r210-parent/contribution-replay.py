#!/usr/bin/env python3
"""Read-only contribution intake; all mutation controls use tiny parent copies."""
from pathlib import Path
import datetime, hashlib, json, shutil, stat, subprocess, tempfile
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]
A=C/'fresh-structural-discovery-r210'; R=C/'structural-r210-contribution-r1'; K=R/'packet'
read=lambda p:json.loads(p.read_bytes()); sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'a3febf90a3f21f1731bca8ea013de99e17be3de2588a0d76f41baf9e51875d8f','MANIFEST':'361e3356c31d104ca364596aa6a371b5132532ba3cdd5b161615880255f1463d','REPORT':'f2b0a8792699402c2ca2592d3fc0e2367d9d01966613ae797b8ea62ceaa92ce7'}
def observe(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        assert not p.is_symlink()
        e={'type':'directory' if p.is_dir() else 'file','mode':format(stat.S_IMODE(p.stat().st_mode),'04o')}
        if p.is_file():b=p.read_bytes();e.update(bytes=len(b),sha256=sha(b))
        out['.' if p==root else p.relative_to(root).as_posix()]=e
    return out
def run(verifier,root,a):
    args=['python3','-I','-B',str(verifier),'--packet',str(root/'packet'),'--manifest',str(root/'MANIFEST.json'),'--report',str(root/'REPORT.md')]
    for k in ['FINAL','MANIFEST','REPORT']:args.extend(['--'+k.lower()+'-sha256',a[k]])
    return subprocess.run(args,capture_output=True,text=True)
before=observe(R); author_before=observe(A); assert author_before==read(P/'observed-root.json')
assert sha((R/'verify_packet.py').read_bytes())=='dae1370f5eb10a00c928cf2423cb8ac8424d71d9b1efb0669d638ce420521c10'
assert (R/'verify_packet.py').read_bytes()==(K/'artifact/verify_packet.py').read_bytes()
v=run(R/'verify_packet.py',R,anchors); assert v.returncode==0,(v.stdout,v.stderr)
av=run(A/'verify_packet.py',A,read(P/'replay.json')['anchors']); assert av.returncode==0,(av.stdout,av.stderr)
copies=read(K/'private/author-input-baseline.json')['files']; assert len(copies)==94
prefix=A.relative_to(PROJECT).as_posix()+'/'
for e in copies:
    assert e['path'].startswith(prefix); rel=e['path'][len(prefix):]; assert rel in author_before
    b=(PROJECT/e['path']).read_bytes(); assert b==(K/'private/author'/rel).read_bytes()
    assert len(b)==e['size'] and sha(b)==e['sha256'] and int(author_before[rel]['mode'],8)==int(e['mode'],8)
tb=(PROJECT/'sources/preprints-tree.json').read_bytes(); assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(tb)['tree']; folder='preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/'
selection=[e for e in tree if e['path'].startswith(folder)]; sources=read(K/'private/source-authentication-independent.json')
assert sources['tree_sha256']==sha(tb) and sources['selection']==selection
blobs=[e for e in selection if e['type']=='blob']; assert len(blobs)==12
for e in blobs:
    b=(K/'private/author/packet/private/source334'/e['path'][len(folder):]).read_bytes()
    assert len(b)==e['size'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['sha']
access=read(K/'private/independent-access/access.json'); bound=0
for e in access:
    if 'access_failure' in e:continue
    assert e['http_status']==200 and e['matches_retained']
    b=(K/'private/independent-access'/e['name']).read_bytes()
    retained=K/'private/author/packet/private'/('primary/'+e['name'] if e['name'].endswith('.pdf') else e['name'])
    assert b==retained.read_bytes() and len(b)==e['bytes'] and sha(b)==e['sha256'];bound+=1
assert bound==7
extracts=0
for e in read(K/'private/independent-access/extraction-verification.json'):
    if e['id']=='nm86-render':continue
    b=(K/'private/independent-access'/f"{e['id']}-independent.txt").read_bytes()
    name='khuri2007-raw.txt' if e['id']=='khuri2007' else e['id']+'.txt'
    assert e['returncode']==0 and len(b)==e['bytes'] and sha(b)==e['sha256'] and b==(K/'private/author/packet/private/primary'/name).read_bytes();extracts+=1
histories=0
for e in read(K/'private/history-authentication-independent.json'):
    assert e['path']=='frontier/campaigns/2026-10-14/fresh-structural-discovery-r22/candidate.md' and (e['start'],e['end']) in [(1520,3282),(3282,4123),(4123,6482)]
    with (PROJECT/e['path']).open('rb') as f:f.seek(e['start']);b=f.read(e['end']-e['start'])
    assert sha(b)==e['sha256'] and b==(K/f"private/author/packet/private/history-r22-{e['start']}-{e['end']}.txt").read_bytes();histories+=1
visual=0
for page in [*range(2,10),*range(11,36)]:
    f=K/f'private/rendered/nm86-{page}.png' if 26<=page<=29 else K/f'private/author/packet/private/primary/nm86-p{page}.png'
    assert f.relative_to(R).as_posix() in before;visual+=1
for page in [5,8,9,10]:
    assert f'packet/private/author/packet/private/primary/khuri2007-p{page}.png' in before;visual+=1
controls=[]
with tempfile.TemporaryDirectory(prefix='contribution-controls-',dir=P) as tmp:
    base=R/'private-controls';ca={'FINAL':sha((base/'packet/FINAL.md').read_bytes()),'MANIFEST':sha((base/'MANIFEST.json').read_bytes()),'REPORT':sha((base/'REPORT.md').read_bytes())}
    for case in ['intact','wrong-anchor','changed-bytes','extra-file','missing-file','file-mode','directory-mode']:
        dst=Path(tmp)/case;shutil.copytree(base,dst);aa=dict(ca);f=dst/'packet/private/sample.txt'
        if case=='wrong-anchor':aa['FINAL']='0'*64
        elif case=='changed-bytes':b=f.read_bytes();f.write_bytes(bytes([b[0]^1])+b[1:])
        elif case=='extra-file':(dst/'packet/extra.txt').write_text('extra\n')
        elif case=='missing-file':f.unlink()
        elif case=='file-mode':f.chmod(stat.S_IMODE(f.stat().st_mode)^0o100)
        elif case=='directory-mode':(dst/'packet').chmod(stat.S_IMODE((dst/'packet').stat().st_mode)^0o020)
        q=run(R/'verify_packet.py',dst,aa);accepted=q.returncode==0;assert accepted==(case=='intact'),(case,q.stdout,q.stderr)
        controls.append({'case':case,'accepted':accepted,'expected':case=='intact'})
assert observe(R)==before and observe(A)==author_before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':json.loads(v.stdout),'author_verification':json.loads(av.stdout),'review_files':sum(e['type']=='file' for e in before.values()),'review_directories':sum(e['type']=='directory' for e in before.values()),'author_files_unchanged':sum(e['type']=='file' for e in author_before.values()),'review_originals_unchanged':True,'retained_input_bindings':len(copies),'canonical_blob_bindings':12,'independent_access_identity_bindings':bound,'extraction_identity_bindings':extracts,'original_history_spans':histories,'visual_record_identity_bindings':visual,'copied_controls':controls,'limits':'Parent read complete REVIEW, FINAL, REPORT, READ-LIMITS, working mathematics and verifier. Underlying source, primary, history, comparator bodies and renders were identity-bound only. Reviewer semantic and visual coverage remains attributed; no inherited reading, new parent primary retrieval, or formal endpoint coverage. Artifact checks do not establish mathematical correctness or substantiality.'}
for name,value in [('contribution-replay.json',out),('contribution-observed-root.json',before)]:
    p=P/name;p.write_text(json.dumps(value,indent=2)+'\n');p.chmod(0o600)
print(json.dumps(out,indent=2))
