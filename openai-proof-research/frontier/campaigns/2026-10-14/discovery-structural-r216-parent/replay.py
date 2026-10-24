#!/usr/bin/env python3
"""Read-only artifact intake. No mathematical certification or inherited reading."""
from pathlib import Path
import datetime, hashlib, json, shutil, stat, subprocess, tempfile
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]
A=C/'fresh-structural-discovery-r216'; K=A/'packet'
read=lambda p:json.loads(p.read_bytes()); sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'4e964c6db78a31d059ff53c759678dd950123ec3eecd148f85c28f3138bd3904','MANIFEST':'79b83e99ccdb5b71cdf87d94b6c17f995b71fc541b5b00e9afe4ec7d21a8d2ca','SELECTION':'0420dc741ef478b059f206645e49a8847cc5650f63e783995563ea3a0cc50231','REPORT':'ad74cf92b45b6eef94070827ad9cd076435805484e4ea05ce92fb4566882f086'}
def observe(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        assert not p.is_symlink()
        e={'type':'directory' if p.is_dir() else 'file','mode':format(stat.S_IMODE(p.stat().st_mode),'04o')}
        if p.is_file():
            b=p.read_bytes();e.update(bytes=len(b),sha256=sha(b))
        out['.' if p==root else p.relative_to(root).as_posix()]=e
    return out
def run(root,a):
    args=['python3','-I','-B',str(A/'verify_packet.py'),'--packet',str(root/'packet')]
    for name in ['manifest','selection','report']:args.extend(['--'+name,str(root/(name.upper()+('.md' if name=='report' else '.json')))])
    for name in ['FINAL','MANIFEST','SELECTION','REPORT']:args.extend(['--'+name.lower()+'-sha',a[name]])
    return subprocess.run(args,capture_output=True,text=True)
before=observe(A)
assert sha((A/'verify_packet.py').read_bytes())=='feadd08d338035715987e81fdd1b142f82fe0a5db541b95d28385aed7d2fbc20'
v=run(A,anchors);assert v.returncode==0,(v.stdout,v.stderr)
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree={e['path']:e for e in json.loads(tb)['tree']};source=read(K/'private/authentication.json')
prefix='preprints/A-counterexample-to-the-nearby-Lagrangian-conjecture-September-23-2026/'
assert len(source)==13 and {e['path'] for e in source}=={p for p,e in tree.items() if e['type']=='blob' and p.startswith(prefix)}
reads=[json.loads(s) for s in (K/'private/reads.jsonl').read_text().splitlines()];textcount=textbytes=0
for e in source:
    local=K/e['local'];assert local.is_relative_to(K);b=local.read_bytes();t=tree[e['path']]
    assert len(b)==e['bytes']==t['size'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==t['sha']
    if local.suffix=='.pdf':continue
    intervals=sorted((r['start'],r['end']) for r in reads if r.get('file')==e['local']);end=0
    for lo,hi in intervals:assert 0<=lo<=end and lo<=hi<=len(b);end=max(end,hi)
    assert end==len(b);textcount+=1;textbytes+=len(b)
assert textcount==12
pdfs=0
for e in read(K/'private/primary/access.json')+read(K/'private/primary/additional-access.json'):
    if 'sha256' not in e:continue
    b=(K/'private/primary'/(e['name']+'.pdf')).read_bytes()
    assert len(b)==e['bytes'] and sha(b)==e['sha256']
    assert len((K/'private/primary'/(e['name']+'.txt')).read_bytes())==e['text_bytes'];pdfs+=1
extents=visuals=0
for e in reads:
    if e.get('file','').startswith('private/primary/'):
        b=(K/e['file']).read_bytes();assert 0<=e['start']<=e['end']<=len(b) and not e['truncated'];extents+=1
    elif e['kind']=='visual read completed':
        for f in e['files']:assert (K/f).is_file();visuals+=1
assert pdfs==6 and extents==17 and visuals==3
controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as tmp:
    base=A/'copied-controls'
    ca={key:sha((base/('packet/FINAL.md' if key=='FINAL' else key+('.md' if key=='REPORT' else '.json'))).read_bytes()) for key in anchors}
    for case in ['intact','wrong-anchor','changed-bytes','extra-file','missing-file','file-mode','directory-mode']:
        dst=Path(tmp)/case;shutil.copytree(base,dst);aa=dict(ca);f=dst/'packet/STATEMENT.md'
        if case=='wrong-anchor':aa['FINAL']='0'*64
        elif case=='changed-bytes':b=f.read_bytes();f.write_bytes(bytes([b[0]^1])+b[1:])
        elif case=='extra-file':(dst/'packet/extra.txt').write_text('extra\n')
        elif case=='missing-file':f.unlink()
        elif case=='file-mode':f.chmod(0o444)
        elif case=='directory-mode':(dst/'packet').chmod(0o755)
        r=run(dst,aa);accepted=r.returncode==0;assert accepted==(case=='intact'),(case,r.stdout,r.stderr)
        controls.append({'case':case,'accepted':accepted,'expected':case=='intact'})
assert observe(A)==before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'statement_sha256':sha((K/'STATEMENT.md').read_bytes()),'proof_sha256':sha((K/'AUTHOR-PROOF.md').read_bytes()),'verification':json.loads(v.stdout),'selected_subdirectories':sum(e['kind']=='dir' for e in read(A/'MANIFEST.json')['entries']),'root_files':sum(e['type']=='file' for e in before.values()),'root_directories':sum(e['type']=='directory' for e in before.values()),'originals_bytes_modes_unchanged':True,'canonical_blobs':13,'full_text_read_record_bindings':textcount,'textual_bytes_recorded':textbytes,'primary_pdf_bindings':pdfs,'primary_extent_identity_bindings':extents,'visual_identity_bindings':visuals,'original_history_bodies_read_by_author':0,'formal_navigation':'Exact pinned lean/docs/340.md returned HTTP404; no formal support.','copied_controls':controls,'limits':'Parent read complete frozen statement, author proof, three analysis notes, FINAL, REPORT, reading limits and verifier. Source/primary bodies identity-bound only, without inherited semantic reading. Author late AIS section 2.4 read, version/access/OCR/unread-intermediate limits and accidental editorial exposures remain disclosed. No history clearance, mathematical grade or formal support.'}
for name,value in [('replay.json',out),('observed-root.json',before)]:
    p=P/name;p.write_text(json.dumps(value,indent=2)+'\n');p.chmod(0o600)
print(json.dumps(out,indent=2))
