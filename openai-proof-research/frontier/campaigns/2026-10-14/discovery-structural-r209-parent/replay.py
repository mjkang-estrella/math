#!/usr/bin/env python3
"""Read-only author packet intake; copied controls are parent-local only."""
from pathlib import Path
import datetime,hashlib,json,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2];R=C/'fresh-structural-discovery-r209'
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'13b11eb180e18d43e4c6547a22584a302d34b1926a733998a96ec9ec4a645ff2','MANIFEST':'ae7c68b98f51683f2de147440bc7a793ba25fe113bae72c6a5d0a1a2860e0786','REPORT':'88d9b15f033de298eedba713f4e26406b67eefd30c04e88140257b6889b03371'}
def observe(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        assert not p.is_symlink();e={'type':'directory' if p.is_dir() else 'file','mode':format(stat.S_IMODE(p.stat().st_mode),'04o')}
        if p.is_file():b=p.read_bytes();e.update(bytes=len(b),sha256=sha(b))
        out['.' if p==root else p.relative_to(root).as_posix()]=e
    return out
def run(root,a):
    args=['python3','-I','-B',str(R/'verify_packet.py'),'--root',str(root)]
    for k in ['FINAL','MANIFEST','REPORT']:args.extend(['--'+k.lower()+'-sha256',a[k]])
    return subprocess.run(args,capture_output=True,text=True)
before=observe(R);assert sha((R/'verify_packet.py').read_bytes())=='27a3db9364b7ae2c10446865308375d22edd089cb0e4c9820342de76e5fbe0ef'
v=run(R,anchors);assert v.returncode==0,(v.stdout,v.stderr)
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree={e['path']:e for e in json.loads(tb)['tree']}
canon=read(R/'private/authenticated-source.json');assert len(canon)==14;by_path={e['path']:e for e in canon}
for e in canon:
    p=R/e['local'];assert p.is_relative_to(R);b=p.read_bytes();t=tree[e['path']]
    assert len(b)==e['bytes']==t['size'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==t['sha']
formal=read(R/'private/lean-authentication.json')
for e in formal:
    p=R/'private'/Path(e['path']).name;b=p.read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']
assert (R/'private/333.md').read_bytes()==(R/'private/lean-333.md').read_bytes()
source_reads=read(R/'private/READS.json')
for e in source_reads:
    a,z=e['extent'];assert 0<=a<z<=by_path[e['path']]['bytes']
rereads=read(R/'private/final-rereads.json')['focused_rereads']
for e in rereads:
    b=(R/e['path']).read_bytes();assert sha(b)==e['sha256'];lo,hi=e['byte_interval'];a,z=e['line_interval_inclusive'];assert b[lo:hi]==b''.join(b.splitlines(keepends=True)[a-1:z])
primary=read(R/'private/primary-read-extents.json')['reads'];extents=0;renders=0
for e in primary:
    b=(R/'private/primary'/(e['name']+'.pdf')).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256']
    txt=(R/'private/primary'/(e['name']+'.txt')).read_bytes();assert sha(txt)==e['extracted_text_sha256'];pages=txt.split(b'\x0c');positions=[];at=0
    for page in pages:positions.append((at,at+len(page)));at+=len(page)+1
    for x in e['exact_extracted_read_extents']:
        assert positions[x['pdf_page_one_based']-1]==(x['extracted_byte_start'],x['extracted_byte_end']);extents+=1
    for page in e.get('visual_pdf_pages',[]):assert (R/'private/primary'/f"{e['name']}-view-{page:02d}.png").is_file();renders+=1
hist=read(R/'private/history-read-extents.json')['selected']
for e in hist:
    with (PROJECT/e['path']).open('rb') as f:f.seek(e['start']);b=f.read(e['end']-e['start'])
    assert sha(b)==e['sha256'] and b==(R/f"private/original-r107-{e['start']}-{e['end']}.txt").read_bytes()
for src,lo,hi,copy,h in [('frontier/NEW-TEN-2026-10-14.md',4801,6347,'acceptance.txt','f147924a01d36cce7ad5ee13bad6ed9ed9109f3bf4b5c2386fc318aae1330984'),('sources/CONTENTS.md',563875,564751,'private/Source333-catalogue.txt','1060cb93bd230f2d1c6f2826d1462bb362e1cd7cd4bdd7b92e82769e62b74217')]:
    with (PROJECT/src).open('rb') as f:f.seek(lo);b=f.read(hi-lo)
    assert sha(b)==h and b==(R/copy).read_bytes()
controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as tmp:
    base=R/'private/integrity-control';ca={k:sha((base/(k+'.md' if k in ['FINAL','REPORT'] else 'MANIFEST.json')).read_bytes()) for k in anchors}
    for case in ['intact','wrong-anchor','changed-bytes','extra-file','missing-file','file-mode','directory-mode']:
        dst=Path(tmp)/case;shutil.copytree(base,dst);aa=dict(ca);f=dst/'payload.txt'
        if case=='wrong-anchor':aa['FINAL']='0'*64
        elif case=='changed-bytes':b=f.read_bytes();mode=stat.S_IMODE(f.stat().st_mode);f.chmod(0o600);f.write_bytes(bytes([b[0]^1])+b[1:]);f.chmod(mode)
        elif case=='extra-file':(dst/'extra.txt').write_text('extra\n')
        elif case=='missing-file':f.unlink()
        elif case=='file-mode':f.chmod(stat.S_IMODE(f.stat().st_mode)^0o100)
        elif case=='directory-mode':dst.chmod(stat.S_IMODE(dst.stat().st_mode)^0o020)
        q=run(dst,aa);accepted=q.returncode==0;assert accepted==(case=='intact'),(case,q.stdout,q.stderr);controls.append({'case':case,'accepted':accepted,'expected':case=='intact'})
assert observe(R)==before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'frozen_sha256':sha((R/'FROZEN-STATEMENT.md').read_bytes()),'proof_sha256':sha((R/'AUTHOR-PROOF.md').read_bytes()),'verification':json.loads(v.stdout),'root_files':sum(e['type']=='file' for e in before.values()),'root_directories':sum(e['type']=='directory' for e in before.values()),'originals_bytes_modes_unchanged':True,'canonical_blobs':len(canon),'formal_bindings':len(formal),'source_extent_metadata_bindings':len(source_reads),'source_reread_bindings':len(rereads),'primary_pdf_bindings':len(primary),'primary_extent_bindings':extents,'history_exact_spans':len(hist),'direct_input_spans':2,'render_integrity_only':renders,'copied_controls':controls,'limits':'Parent read complete original statement, proof, derivations, reading/comparison prose, session, FINAL and REPORT; inspected mode-check code/output without treating them as independent mathematical evidence. Underlying source/primary/history/comparator bodies and renders were identity-bound only; no inherited semantic reading or visual inspection. Comparator metadata bindings use supplied pinned identities, not new parent downloads. No mathematical grade or exhaustive literature/history clearance.'}
for name,value in [('replay.json',out),('observed-root.json',before)]:
    p=P/name;p.write_text(json.dumps(value,indent=2)+'\n');p.chmod(0o600)
print(json.dumps(out,indent=2))
