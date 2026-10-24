#!/usr/bin/env python3
"""Read-only r210 author packet intake and parent-local copied controls."""
from pathlib import Path
import datetime,hashlib,json,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]; R=C/'fresh-structural-discovery-r210'; K=R/'packet'
read=lambda p:json.loads(p.read_bytes()); sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'87df07efcb7f569ad990fb11dc0913788a18bc6240921473a0ef5a35f61a9c07','MANIFEST':'060ac24a4e3f7bf1b63a4c0a405c3dd54491705e7d6f3dfa682db51ee4318b72','REPORT':'dee20f102c1fa46f9ee3c1042caf5308ea8d2c543e9918d6eb5289b61489ea8a'}
def observe(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        assert not p.is_symlink()
        e={'type':'directory' if p.is_dir() else 'file','mode':format(stat.S_IMODE(p.stat().st_mode),'04o')}
        if p.is_file():b=p.read_bytes();e.update(bytes=len(b),sha256=sha(b))
        out['.' if p==root else p.relative_to(root).as_posix()]=e
    return out
def run(root,a):
    args=['python3','-I','-B',str(R/'verify_packet.py'),'--packet',str(root/'packet'),'--manifest',str(root/'MANIFEST.json'),'--report',str(root/'REPORT.md')]
    for k in ['FINAL','MANIFEST','REPORT']:args.extend(['--'+k.lower()+'-sha256',a[k]])
    return subprocess.run(args,capture_output=True,text=True)
before=observe(R)
assert sha((R/'verify_packet.py').read_bytes())=='bb111c71ded0b0dcdd64df4b3fe9aa9883dfa323fd06d1fa01aa2219989cea6a'
v=run(R,anchors); assert v.returncode==0,(v.stdout,v.stderr)
for n in ['AUTHOR-PROOF.md','FROZEN-STATEMENT.md','AUTHOR-CHECK.md','READ-LIMITS.md','FINAL.md']:
    assert (R/n).read_bytes()==(K/n).read_bytes()
assert (R/'verify_packet.py').read_bytes()==(K/'artifact/verify_packet.py').read_bytes()
assert (R/'derivations/00-feasibility.md').read_bytes()==(K/'derivations/00-feasibility.md').read_bytes()
tb=(PROJECT/'sources/preprints-tree.json').read_bytes(); assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree={e['path']:e for e in json.loads(tb)['tree']}; canon=read(K/'private/source-authentication.json'); assert len(canon)==12
for e in canon:
    local=PROJECT/e['local']; assert local.is_relative_to(R/'private')
    b=local.read_bytes(); copy=K/local.relative_to(R); assert b==copy.read_bytes()
    assert len(b)==e['bytes']==tree[e['path']]['size'] and sha(b)==e['sha256']
    assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==tree[e['path']]['sha']
for n in ['334-authentication.json','comparator-authentication.json']:
    e=read(K/'private'/n); b=(K/'private'/Path(e['path']).name).read_bytes()
    assert len(b)==e['bytes'] and sha(b)==e['sha256']
    assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']
primary=read(K/'private/primary-access.json'); primary_bound=0
for e in primary:
    f=K/'private/primary'/(e['id']+'.pdf')
    if f.exists():
        b=f.read_bytes(); assert len(b)==e['bytes'] and sha(b)==e['sha256']; primary_bound+=1
e=read(K/'private/primary/nakamura_maeda1986-access.json'); b=(K/'private/primary/nakamura_maeda1986.pdf').read_bytes(); assert len(b)==e['bytes'] and sha(b)==e['sha256']; primary_bound+=1
hist=read(K/'private/history-read-extents.json')['sections']; assert len(hist)==3
for e in hist:
    assert e['path']=='frontier/campaigns/2026-10-14/fresh-structural-discovery-r22/candidate.md'
    assert (e['start'],e['end']) in [(1520,3282),(3282,4123),(4123,6482)]
    with (PROJECT/e['path']).open('rb') as f:f.seek(e['start']); b=f.read(e['end']-e['start'])
    assert sha(b)==e['sha256'] and b==(K/f"private/history-r22-{e['start']}-{e['end']}.txt").read_bytes()
with (PROJECT/'sources/CONTENTS.md').open('rb') as f:f.seek(564751); b=f.read(1016)
assert sha(b)=='428a5db11e83bdff7f0281a77b4fdb885c4c71518de7fd4ef981235b9a4dde8b' and b==(K/'private/source334-catalogue.txt').read_bytes()
controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as tmp:
    base=R/'controls'; ca={'FINAL':sha((base/'packet/FINAL.md').read_bytes()),'MANIFEST':sha((base/'MANIFEST.json').read_bytes()),'REPORT':sha((base/'REPORT.md').read_bytes())}
    for case in ['intact','wrong-anchor','changed-bytes','extra-file','missing-file','file-mode','directory-mode']:
        dst=Path(tmp)/case; shutil.copytree(base,dst); aa=dict(ca); f=dst/'packet/FROZEN-STATEMENT.md'
        if case=='wrong-anchor':aa['FINAL']='0'*64
        elif case=='changed-bytes':b=f.read_bytes(); f.write_bytes(bytes([b[0]^1])+b[1:])
        elif case=='extra-file':(dst/'packet/extra.txt').write_text('extra\n')
        elif case=='missing-file':f.unlink()
        elif case=='file-mode':f.chmod(stat.S_IMODE(f.stat().st_mode)^0o100)
        elif case=='directory-mode':(dst/'packet').chmod(stat.S_IMODE((dst/'packet').stat().st_mode)^0o020)
        q=run(dst,aa); accepted=q.returncode==0; assert accepted==(case=='intact'),(case,q.stdout,q.stderr)
        controls.append({'case':case,'accepted':accepted,'expected':case=='intact'})
assert observe(R)==before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'frozen_sha256':sha((K/'FROZEN-STATEMENT.md').read_bytes()),'proof_sha256':sha((K/'AUTHOR-PROOF.md').read_bytes()),'verification':json.loads(v.stdout),'root_files':sum(e['type']=='file' for e in before.values()),'root_directories':sum(e['type']=='directory' for e in before.values()),'originals_bytes_modes_unchanged':True,'canonical_blobs':12,'formal_bindings':2,'primary_pdf_bindings':primary_bound,'history_exact_spans':3,'selected_render_integrity_only':sum(e['type']=='file' and name.startswith('packet/') and name.endswith('.png') for name,e in before.items()),'copied_controls':controls,'limits':'Parent read complete original frozen statement, author proof, feasibility, author checks, reading limits, FINAL and REPORT, and inspected verifier/control code. Source, primary, history, comparator and renders were identity-bound only. No inherited semantic/visual reading, fresh primary download, formal endpoint coverage, mathematical grade or exhaustive clearance.'}
for name,value in [('replay.json',out),('observed-root.json',before)]:
    p=P/name; p.write_text(json.dumps(value,indent=2)+'\n'); p.chmod(0o600)
print(json.dumps(out,indent=2))
