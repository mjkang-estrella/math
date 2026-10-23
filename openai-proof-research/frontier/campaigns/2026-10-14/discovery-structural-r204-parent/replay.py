#!/usr/bin/env python3
"""Read-only r204 archive identity checks; mutate only tiny parent-owned copies."""
from pathlib import Path
import datetime,hashlib,json,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2];R=C/'fresh-structural-discovery-r204';S=R/'packet';D=S/'private'
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'6158ac9610607e290d4e4961ecfeed94651fce53a95f61a0a9dd8c3955b7d9d8','MANIFEST':'02a06e93cbb0edfe257d82188f3eaf39ffc95cf04beca2769c53c1bcc1863cb6','REPORT':'c7a01efd6f834e86d97e8b64adb402c73978931514fefca664a4dde1fde43465'}
def observe(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        assert not p.is_symlink();e={'type':'directory' if p.is_dir() else 'file','mode':format(stat.S_IMODE(p.stat().st_mode),'04o')}
        if p.is_file():b=p.read_bytes();e.update(bytes=len(b),sha256=sha(b))
        out['.' if p==root else p.relative_to(root).as_posix()]=e
    return out
def command(root,a):return ['python3','-I','-B',str(S/'verify_packet.py'),'--packet',str(root/'packet'),'--report',str(root/'REPORT.md'),'--final-sha256',a['FINAL'],'--manifest-sha256',a['MANIFEST'],'--report-sha256',a['REPORT']]
def run(args):return subprocess.run(args,capture_output=True,text=True)
before=observe(R)
for k,p in [('FINAL',S/'FINAL.md'),('MANIFEST',S/'MANIFEST.json'),('REPORT',R/'REPORT.md')]:assert sha(p.read_bytes())==anchors[k]
assert (R/'verify_packet.py').read_bytes()==(S/'verify_packet.py').read_bytes()
v=run(command(R,anchors));assert v.returncode==0,(v.stdout,v.stderr)
m=read(S/'MANIFEST.json');assert len(m['files'])==50 and len(m['directories'])==7
for e in m['files']:
    outside=R/e['path'];assert outside.is_file() and outside.read_bytes()==(S/e['path']).read_bytes()
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree={e['path']:e for e in json.loads(tb)['tree']}
auth=read(D/'authenticated.json');assert len(auth['blobs'])==12
for e in auth['blobs']:
    b=(S/e['local']).read_bytes();t=tree[e['path']]
    assert len(b)==e['size']==t['size'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['sha']==t['sha']
formal=[(D/'lean-328.md',auth['lean_doc']),(D/'ReflexiveFixedPoints.lean',read(D/'comparator-metadata.json'))]
for p,e in formal:
    b=p.read_bytes();assert len(b)==e['size'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']
ext=read(D/'read-extents.json');assert len(ext['source_reads'])==14
for e in ext['source_reads']:
    b=(S/e['local']).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256']
    if e['read_extents']:assert e['read_extents']==[[0,len(b)]]
for e in ext['primary_local_reads']:
    b=(D/'primary'/(e['name']+'.txt')).read_bytes();assert sha(b)==e['sha256_text']
    for q in e['selected_extents']:lo,hi=q['text_bytes'];assert 0<=lo<hi<=len(b)
for e in read(D/'primary/access.json'):
    if 'sha256' in e:
        b=(D/'primary'/(e['name']+'.pdf')).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256']
e=read(D/'primary/dominguez-lorenzo-access.json');b=(D/'primary/dominguez-lorenzo2001.pdf').read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256']
e=read(D/'original-history-read.json');lo,hi=e['extent_bytes']
with (PROJECT/e['path']).open('rb') as f:f.seek(lo);b=f.read(hi-lo)
assert len(b)==hi-lo and sha(b)==e['selection_sha256'] and b==(D/'original-i88-section.md').read_bytes()
for path,lo,hi,expected,copied in [('frontier/NEW-TEN-2026-10-14.md',4801,6347,'f147924a01d36cce7ad5ee13bad6ed9ed9109f3bf4b5c2386fc318aae1330984','acceptance.bin'),('sources/CONTENTS.md',554644,555424,'2dfe40065c246cf14c37cad653e9d737cbb53d6ee96b439ba3348c5009e2013e','source328-catalogue.bin')]:
    with (PROJECT/path).open('rb') as f:f.seek(lo);b=f.read(hi-lo)
    assert len(b)==hi-lo and sha(b)==expected and b==(D/copied).read_bytes()
controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as tmp:
    base=R/'copied-controls/baseline';a={'FINAL':sha((base/'packet/FINAL.md').read_bytes()),'MANIFEST':sha((base/'packet/MANIFEST.json').read_bytes()),'REPORT':sha((base/'REPORT.md').read_bytes())}
    for case in ['intact','altered-payload','altered-mode','extra-file','altered-report']:
        dst=Path(tmp)/case;shutil.copytree(base,dst);f=dst/'packet/FINAL.md'
        if case=='altered-payload':b=f.read_bytes();f.chmod(0o644);f.write_bytes(b+b'!');f.chmod(0o444)
        elif case=='altered-mode':f.chmod(0o644)
        elif case=='extra-file':(dst/'packet/unlisted.txt').write_text('extra\n')
        elif case=='altered-report':f=dst/'REPORT.md';f.chmod(0o644);f.write_text('altered\n');f.chmod(0o444)
        q=run(command(dst,a));accepted=q.returncode==0;assert accepted==(case=='intact'),(case,q.stdout,q.stderr);controls.append({'case':case,'accepted':accepted,'expected':case=='intact'})
assert observe(R)==before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':json.loads(v.stdout),'manifest_additional_file':True,'selected_content_bytes':sum(e['bytes'] for e in m['files']),'root_files':sum(e['type']=='file' for e in before.values()),'root_directories':sum(e['type']=='directory' for e in before.values()),'originals_bytes_modes_unchanged':True,'outside_copies_matched_selected_files':50,'canonical_blobs':12,'formal_bindings':2,'source_text_read_extent_bindings':13,'source_pdf_authentication_only':True,'primary_text_bindings':3,'primary_pdf_bindings':3,'cached_primary_access_records':2,'renders_integrity_only':3,'history_exact_spans':1,'catalogue_acceptance_spans':2,'copied_controls':controls,'derivations_sha256':sha((S/'DERIVATIONS.md').read_bytes()),'verifier_sha256':sha((S/'verify_packet.py').read_bytes()),'limits':'Parent read full original derivations, final/report and reading/access metadata, not underlying source/primary/history bodies or renders. Packet selects50 payload files plus separately anchored MANIFEST; seven selected directory modes and outside REPORT mode are checked. Other outside selection/modes are parent observations only. Cached primary text access is not local PDF authentication; clipped manuscript lines remain unavailable. No mathematical grade.'}
for name,value in [('replay.json',out),('observed-root.json',before)]:
    p=P/name;p.write_text(json.dumps(value,indent=2)+'\n');p.chmod(0o600)
print(json.dumps(out,indent=2))
