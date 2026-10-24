#!/usr/bin/env python3
"""Read-only artifact intake; no mathematical certification or inherited reading."""
from pathlib import Path
import datetime,hashlib,json,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2];A=C/'fresh-structural-discovery-r215'
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'b1f2a268132eedc4c629bed54ba5d98a6a74b2e3fd2a75c5905835c44333731c','MANIFEST':'7f9d0ce86d987efa2a7e02fb35c483ce614b09e7946ce30474551d455cccd5df','REPORT':'a5ff5141ee13ca09bc7b95e663e00dd02681e05fde3817fed8af9d8883811571'}
def observe(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        assert not p.is_symlink();e={'type':'directory' if p.is_dir() else 'file','mode':format(stat.S_IMODE(p.stat().st_mode),'04o')}
        if p.is_file():b=p.read_bytes();e.update(bytes=len(b),sha256=sha(b))
        out['.' if p==root else p.relative_to(root).as_posix()]=e
    return out
def run(root,a):
    args=['python3','-I','-B',str(A/'verify_packet.py'),'--base',str(root)]
    for k in ['FINAL','MANIFEST','REPORT']:args.extend(['--'+k.lower()+'-sha256',a[k]])
    return subprocess.run(args,capture_output=True,text=True)
before=observe(A);assert sha((A/'verify_packet.py').read_bytes())=='17b8566496d5464a896b65248632d6390d3a3d13dde59610de92022f8331cb3e'
v=run(A,anchors);assert v.returncode==0,(v.stdout,v.stderr)
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree={e['path']:e for e in json.loads(tb)['tree']};source=read(A/'private/source-authentication.json');coverage=read(A/'private/coverage-arithmetic.json');assert len(source)==12 and len(coverage)==11
prefix='preprints/Entropy-equality-and-local-symmetry-in-negative-curvature-September-23-2026/'
assert {e['path'] for e in source}=={p for p,e in tree.items() if e['type']=='blob' and p.startswith(prefix)}
for e in source:
    local=PROJECT/e['local'];assert local.is_relative_to(A);b=local.read_bytes();t=tree[e['path']]
    assert len(b)==e['bytes']==t['size'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==t['sha']
exts=[json.loads(line) for line in (A/'private/semantic-reads.jsonl').read_text().splitlines()];textbytes=0
for e in coverage:
    b=(A/'private/source'/e['file']).read_bytes();assert len(b)==e['bytes'] and e['logged_byte_union']=='complete'
    intervals=sorted((x['byte_start'],x['byte_end']) for x in exts if x['file']==e['file']);end=0
    for lo,hi in intervals:assert 0<=lo<=end and lo<=hi<=len(b);end=max(end,hi)
    assert end==len(b);textbytes+=len(b)
primary=0
access=read(A/'private/primary-access.json')+read(A/'private/primary-access-recovery.json')+[read(A/'private/flaminio-archive-access.json'),dict(read(A/'private/contreras-access.json'),name='contreras')]
for e in access:
    if 'sha256' not in e:continue
    b=(A/'private/primary'/(e['name']+'.pdf')).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256'];primary+=1
primary_extents=0
for line in (A/'private/primary-semantic-reads.jsonl').read_text().splitlines():
    e=json.loads(line);assert '/' not in e['name'];b=(A/'private/primary'/(e['name']+'.txt')).read_bytes();lo,hi=e['byte_extent'];assert sha(b)==e['extraction_sha256'] and 0<=lo<=hi<=len(b);primary_extents+=1
e=read(A/'private/history-semantic-reads.json');assert e['path']=='frontier/campaigns/2026-10-14/fresh-analytic-discovery-r31/339-feasibility.md' and e['extent']==[366,6270]
with (PROJECT/e['path']).open('rb') as f:f.seek(366);b=f.read(6270-366)
assert b==(A/'private/history-original-r31-selected.txt').read_bytes()
controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as tmp:
    base=A/'controls';assert (base/'sample.txt').read_bytes()==(A/'verify_packet.py').read_bytes()
    ca={'FINAL':sha((base/'FINAL.md').read_bytes()),'MANIFEST':sha((base/'MANIFEST.json').read_bytes()),'REPORT':sha((base/'REPORT.md').read_bytes())}
    for case in ['intact','wrong-anchor','changed-bytes','extra-file','missing-file','file-mode','directory-mode']:
        dst=Path(tmp)/case;shutil.copytree(base,dst);aa=dict(ca);f=dst/'sample.txt'
        if case=='wrong-anchor':aa['FINAL']='0'*64
        elif case=='changed-bytes':b=f.read_bytes();f.write_bytes(bytes([b[0]^1])+b[1:])
        elif case=='extra-file':(dst/'extra.txt').write_text('extra\n');(dst/'extra.txt').chmod(0o600)
        elif case=='missing-file':f.unlink()
        elif case=='file-mode':f.chmod(0o444)
        elif case=='directory-mode':dst.chmod(0o755)
        r=run(dst,aa);accepted=r.returncode==0;assert accepted==(case=='intact'),(case,r.stdout,r.stderr)
        controls.append({'case':case,'accepted':accepted,'expected':case=='intact'})
assert observe(A)==before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':json.loads(v.stdout),'selected_subdirectories':len(read(A/'MANIFEST.json')['directories']),'root_files':sum(e['type']=='file' for e in before.values()),'root_directories':sum(e['type']=='directory' for e in before.values()),'originals_bytes_modes_unchanged':True,'canonical_blobs':12,'full_text_read_record_bindings':11,'textual_bytes_recorded':textbytes,'primary_pdf_bindings':primary,'primary_extent_identity_bindings':primary_extents,'exact_original_history_span_bindings':1,'formal_navigation':read(A/'private/lean-navigation-access.json'),'copied_controls':controls,'limits':'Parent read complete DERIVATIONS, FINAL, REPORT, private/READING and verifier. Underlying source/primary/history bodies were identity-bound only, without inherited semantic reading. Source bibliography truncation recovery, primary OCR/unread-intermediate/access limits, accidental cover/footnote exposures and redundant late narrow navigation remain disclosed. No exhaustive history clearance, mathematical grade or formal support.'}
for name,value in [('replay.json',out),('observed-root.json',before)]:
    p=P/name;p.write_text(json.dumps(value,indent=2)+'\n');p.chmod(0o600)
print(json.dumps(out,indent=2))
