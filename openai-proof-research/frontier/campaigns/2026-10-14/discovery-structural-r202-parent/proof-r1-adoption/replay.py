#!/usr/bin/env python3
"""Read-only correctness packet checks; mutate only tiny parent-owned copies."""
from pathlib import Path
import datetime,hashlib,json,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent;C=P.parents[1];PROJECT=C.parents[2]
R=C/'structural-r202-proof-r1';A=C/'fresh-structural-discovery-r202'
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest();mode=lambda p:format(stat.S_IMODE(p.stat().st_mode),'04o')
anchors={'FINAL.json':'689e1cbeaca6276c55062e6517cbc742c161a93f9eb7b3fc06741b2d31a7d24e','MANIFEST.json':'4ffd676bbde440065ac1430715b72eac9bb7a793092b430c4dd629d4d8b053d4','REPORT.md':'ad59dd65bcf36a6b2835cdd71c1a339b97be78ee0203764e538c219df22f2438'}
def observe(root):
    out={'.':{'mode':mode(root),'type':'directory'}}
    for p in sorted(root.rglob('*')):
        assert not p.is_symlink();e={'type':'directory' if p.is_dir() else 'file','mode':mode(p)}
        if p.is_file():b=p.read_bytes();e.update(bytes=len(b),sha256=sha(b))
        out[p.relative_to(root).as_posix()]=e
    return out
def verify(root,a):
    return subprocess.run(['python3','-I','-B',str(R/'verify_packet.py'),'--root',str(root),'--final-sha256',a['FINAL.json'],'--manifest-sha256',a['MANIFEST.json'],'--report-sha256',a['REPORT.md']],capture_output=True,text=True)
before=observe(R);ab=observe(A);assert ab==read(P.parent/'observed-root.json')
v=verify(R,anchors);assert v.returncode==0,(v.stdout,v.stderr)
m=read(R/'MANIFEST.json');f=read(R/'FINAL.json');assert f['correctness_verdict']=='PASS' and not f['essential_repairs'] and not f['unresolved_frozen_mathematical_obligations']
assert len(m['files'])==30 and len(m['directories'])==7 and sum(e['bytes'] for e in m['files'])==142371
assert (R/'private/author-FROZEN-STATEMENT.md').read_bytes()==(A/'FROZEN-STATEMENT.md').read_bytes()
assert (R/'private/author-AUTHOR-PROOF.md').read_bytes()==(A/'AUTHOR-PROOF.md').read_bytes()
assert sha((A/'FROZEN-STATEMENT.md').read_bytes())==f['reviewed_frozen_sha256'] and sha((A/'AUTHOR-PROOF.md').read_bytes())==f['reviewed_author_proof_sha256']
after=read(R/'private/author-after.json');selected=read(R/'private/author-selected-before.json');outside=read(R/'private/author-outside-before.json')
assert after['selected']==selected and after['outside']==outside and after['author_verifier_exit']==0
for e in selected:assert ab[e['path']]==dict(type='file',**{k:e[k] for k in ['bytes','sha256','mode']})
for name,e in outside.items():assert ab[name]==dict(type='file',bytes=e['size'],sha256=e['sha256'],mode=format(int(e['mode'],8),'04o'))
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree={e['path']:e for e in json.loads(tb)['tree']}
canon=read(R/'private/canonical-authentication.json')['entries'];assert len(canon)==10
for e in canon:
    b=(PROJECT/e['local']).read_bytes();t=tree[e['upstream']]
    assert len(b)==e['bytes']==t['size'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==t['sha']
for e,name in zip(read(R/'private/lean-authentication.json'),['lean326.md','Cotype.lean']):
    b=(R/'private'/name).read_bytes();assert b==(A/'private'/name).read_bytes() and len(b)==e['bytes'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']
primary=read(R/'private/primary-authentication.json')['pdfs'];assert len(primary)==8
for e in primary:
    b=(A/'private/primary'/(e['key']+'.pdf')).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256']
reading=read(R/'private/reading-record.json')
for e in reading['canonical']:
    b=(A/e['path']).read_bytes();assert e['bytes']==[0,len(b)] and sha(b)==e['sha256']
for e in reading['history']+[x for x in reading['direct'] if 'bytes' in x]:
    lo,hi=e['bytes']
    with (PROJECT/e['path']).open('rb') as stream:stream.seek(lo);b=stream.read(hi-lo)
    assert len(b)==hi-lo and sha(b)==e['sha256']
controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as tmp:
    for name in ['exact','bytes','file-mode','directory-mode','extra-directory','extra-file','outside-mode','wrong-anchor']:
        dst=Path(tmp)/name;shutil.copytree(R/'controls/good',dst)
        a=dict(line.split() for line in (dst/'ANCHORS.txt').read_text().splitlines());payload=dst/'data/payload.txt'
        if name=='bytes':payload.chmod(0o644);payload.write_bytes(payload.read_bytes()+b'!');payload.chmod(0o444)
        elif name=='file-mode':payload.chmod(0o400)
        elif name=='directory-mode':(dst/'data').chmod(0o500)
        elif name=='extra-directory':dst.chmod(0o755);(dst/'empty').mkdir();dst.chmod(0o555)
        elif name=='extra-file':dst.chmod(0o755);(dst/'extra.txt').write_text('extra');dst.chmod(0o555)
        elif name=='outside-mode':(dst/'REPORT.md').chmod(0o400)
        elif name=='wrong-anchor':a['FINAL.json']='0'*64
        q=verify(dst,a);assert (q.returncode==0)==(name=='exact'),(name,q.stdout,q.stderr)
        controls.append({'case':name,'accepted':q.returncode==0,'expected':name=='exact','stdout':q.stdout.strip()})
        for p in dst.rglob('*'):
            if p.is_dir():p.chmod(0o700)
        dst.chmod(0o700)
assert observe(R)==before and observe(A)==ab
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':json.loads(v.stdout),'selected_bytes':142371,'root_files':34,'root_directories':7,'author_files':123,'author_directories':10,'author_bytes_modes_unchanged':True,'review_bytes_modes_unchanged':True,'canonical_bindings':10,'canonical_text_reading_bindings':9,'formal_bindings':2,'primary_pdf_bindings':8,'history_spans':3,'catalogue_acceptance_spans':2,'copied_controls':controls,'review_sha256':f['selected_target']['sha256'],'frozen_statement_sha256':f['reviewed_frozen_sha256'],'author_proof_sha256':f['reviewed_author_proof_sha256'],'limits':'Authentication is not semantic reading. Parent read full review/reconstruction/limits and metadata; source/primary/history bodies were not semantically reread at this intake. Author manifest does not bind directory/outside-file modes; parent original baseline independently does. Review binds its exact file/directory set and modes including outside-file modes.'}
for name,value in [('replay.json',out),('observed-root.json',before)]:
    p=P/name;p.write_text(json.dumps(value,indent=2)+'\n');p.chmod(0o600)
print(json.dumps(out,indent=2))
