#!/usr/bin/env python3
"""Read-only identity intake of a non-nominee; tiny controls stay parent-local."""
from pathlib import Path
import datetime,hashlib,json,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]; R=C/'fresh-structural-discovery-r208'; S=R/'packet'
read=lambda p:json.loads(p.read_bytes()); sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'5a7fa07720d4d89b84e6a11603f27b4b0c6f80929f04f4c6676264def02e48ac','MANIFEST':'4d6ae7a8aa3156d3345dcd6b0c0280741dff7565b64ec5341511b6a0db1b7899','REPORT':'351e93f583f48af3df8738a9dde8a79842df3d2df5db7c2d6c0e1109cfc801d7'}
def observe(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        assert not p.is_symlink(); e={'type':'directory' if p.is_dir() else 'file','mode':format(stat.S_IMODE(p.stat().st_mode),'04o')}
        if p.is_file(): b=p.read_bytes();e.update(bytes=len(b),sha256=sha(b))
        out['.' if p==root else p.relative_to(root).as_posix()]=e
    return out
def run(root,a):
    args=['python3','-I','-B',str(S/'verify_packet.py'),'--root',str(root)]
    for k in ['FINAL','MANIFEST','REPORT']:args.extend(['--'+k.lower()+'-sha256',a[k]])
    return subprocess.run(args,capture_output=True,text=True)
before=observe(R);assert sha((S/'verify_packet.py').read_bytes())=='80777be753da887238e1126cd3bc2cd0dc617e414319996cfbb00e06300ce8d3'
v=run(R,anchors);assert v.returncode==0,(v.stdout,v.stderr)
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree={e['path']:e for e in json.loads(tb)['tree']}
canon=read(S/'private/source-authentication.json');assert len(canon)==4
for e in canon:
    p=PROJECT/e['path'];assert p.is_relative_to(S);b=p.read_bytes();key='preprints/'+e['url'].split('/preprints/',1)[1];t=tree[key]
    assert len(b)==e['size']==t['size'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==t['sha']
access=[]
for name in ['access.json','additional-access.json','third-access.json']:
    access += [e for e in read(S/'private/primary'/name) if 'sha256' in e]
for e in access:
    b=(S/'private/primary'/e.get('file',e.get('name'))).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256']
extents=read(S/'private/primary-read-extents.json');n_extents=0
for e in extents:
    b=(S/e['file']).read_bytes();assert sha(b)==e['sha256'];pages=b.split(b'\x0c');positions=[];at=0
    for page in pages:positions.append((at,at+len(page)));at+=len(page)+1
    for num,span in zip(e['read_pdf_pages'],e['text_byte_extents'],strict=True):assert positions[num-1]==tuple(span);n_extents+=1
hist=read(S/'private/history-read-extents.json');bound=0
for index in [0,1,3]:
    e=hist[index]
    with (PROJECT/e['path']).open('rb') as f:f.seek(e['byte_start']);b=f.read(e['byte_end']-e['byte_start'])
    assert sha(b)==e['section_sha256'] and b==(S/f'private/original-section-{index+1:02d}.txt').read_bytes();bound+=1
scopes=read(S/'private/history-scope-extents.json')
for num,e in zip([41,42],scopes,strict=True):
    lo,hi=e['extent']
    with (PROJECT/e['path']).open('rb') as f:f.seek(lo);b=f.read(hi-lo)
    assert sha(b)==e['sha256'] and b==(S/f'private/original-scope-r{num}.txt').read_bytes()
for src,lo,hi,copy,h in [('frontier/NEW-TEN-2026-10-14.md',4801,6347,'acceptance-excerpt.txt','f147924a01d36cce7ad5ee13bad6ed9ed9109f3bf4b5c2386fc318aae1330984'),('sources/CONTENTS.md',562805,563875,'source332-catalogue.txt','f9e29c49ccfebd251d9163b4dfadbce47affe2ce676bc5fd0968e72ab412cd2a')]:
    with (PROJECT/src).open('rb') as f:f.seek(lo);b=f.read(hi-lo)
    assert sha(b)==h and b==(S/'private'/copy).read_bytes()
controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as tmp:
    base=S/'private/tiny-controls/fixture';ca=read(S/'private/tiny-controls/anchors.json')
    for case in ['intact','wrong-anchor','changed-bytes','extra-file','missing-file','file-mode','directory-mode']:
        dst=Path(tmp)/case;shutil.copytree(base,dst);aa=dict(ca);f=dst/'packet/payload.txt'
        if case=='wrong-anchor':aa['FINAL']='0'*64
        elif case=='changed-bytes':b=f.read_bytes();f.chmod(0o644);f.write_bytes(bytes([b[0]^1])+b[1:]);f.chmod(0o444)
        elif case in ['extra-file','missing-file']:
            (dst/'packet').chmod(0o755)
            if case=='extra-file':(dst/'packet/extra.txt').write_text('extra\n')
            else:f.unlink()
            (dst/'packet').chmod(0o555)
        elif case=='file-mode':f.chmod(0o644)
        elif case=='directory-mode':(dst/'packet').chmod(0o755)
        q=run(dst,aa);accepted=q.returncode==0;assert accepted==(case=='intact'),(case,q.stdout,q.stderr);controls.append({'case':case,'accepted':accepted,'expected':case=='intact'})
assert observe(R)==before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':json.loads(v.stdout),'root_files':sum(e['type']=='file' for e in before.values()),'root_directories':sum(e['type']=='directory' for e in before.values()),'originals_bytes_modes_unchanged':True,'canonical_blobs':4,'primary_pdf_bindings':len(access),'primary_extent_bindings':n_extents,'history_exact_mathematical_spans':bound,'original_scope_bindings':len(scopes),'disclosed_false_admissions_not_semantically_reread':True,'direct_input_spans':2,'render_integrity_only':4,'formal_endpoint_bindings':0,'copied_controls':controls,'limits':'Parent read complete original DERIVATIONS, READING, FINAL and REPORT; recovered the truncated combined display with a bounded repeat covering sections4-7. Underlying source/primary/history bodies and renders were identity-bound only, with no inherited semantic reading or visual inspection. Formal navigation access failure leaves endpoints unverified. No correctness/contribution grade or exhaustive clearance.'}
for name,value in [('replay.json',out),('observed-root.json',before)]:
    p=P/name;p.write_text(json.dumps(value,indent=2)+'\n');p.chmod(0o600)
print(json.dumps(out,indent=2))
