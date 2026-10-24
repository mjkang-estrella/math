#!/usr/bin/env python3
"""Read-only artifact intake, without mathematical certification or inherited reading."""
from pathlib import Path
import datetime,hashlib,json,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2];A=C/'fresh-structural-discovery-r214'
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'5b07fe80fa9a0a75751cf7acf04aadbad17fd964e4a8407d08f99c3f0892b718','MANIFEST':'55c4fbfe55d62f71f5b3b49cd3a0a8a3809f0eaf986b358bca0693a1c047e48f','REPORT':'c404764f80aeb6afa4cb420ed2ac2e0ed3de609c5513f5c69957e5182630f1d7'}
def observe(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        assert not p.is_symlink();e={'type':'directory' if p.is_dir() else 'file','mode':format(stat.S_IMODE(p.stat().st_mode),'04o')}
        if p.is_file():b=p.read_bytes();e.update(bytes=len(b),sha256=sha(b))
        out['.' if p==root else p.relative_to(root).as_posix()]=e
    return out
def run(root,a):
    args=['python3','-I','-B',str(root/'verify_packet.py'),'--root',str(root)]
    for k in ['FINAL','MANIFEST','REPORT']:args.extend(['--'+k.lower()+'-sha256',a[k]])
    return subprocess.run(args,capture_output=True,text=True)
before=observe(A);assert sha((A/'verify_packet.py').read_bytes())=='e282dcc9fad558cd2e8dd0851398af4f3a72e4cb8836110a7e86d72f2124bfb8'
v=run(A,anchors);assert v.returncode==0,(v.stdout,v.stderr)
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree={e['path']:e for e in json.loads(tb)['tree']};source=read(A/'private/source-authentication.json');coverage=read(A/'private/final-reading-record.json');assert len(source)==14
prefix='preprints/Uniformization-of-complete-Kahler-manifolds-with-positive-bisectional-curvature-September-23-2026/'
assert {e['path'] for e in source}=={p for p,e in tree.items() if e['type']=='blob' and p.startswith(prefix)}
for e in source:
    b=(A/e['local']).read_bytes();t=tree[e['path']]
    assert len(b)==e['bytes']==t['size'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==t['sha']
texts=0;textbytes=0
for name,intervals in coverage['source_full_text_unions'].items():
    b=(A/name).read_bytes();assert intervals==[[0,len(b)]];texts+=1;textbytes+=len(b)
assert texts==13 and {e['local'] for e in source if not e['local'].endswith('.pdf')}==set(coverage['source_full_text_unions'])
for line in (A/'private/read-extents.jsonl').read_text().splitlines():
    e=json.loads(line);b=(A/e['file']).read_bytes();assert sha(b)==e['sha256'] and len(b)==e['total'] and 0<=e['start']<=e['stop']<=len(b)
primary=0
access=read(A/'private/primary/access.json')+read(A/'private/primary/symmetry-access.json')+[dict(read(A/'private/primary/BerndtssonRosay-access.json'),name='BerndtssonRosay')]
for e in access:
    if 'sha256' not in e:continue
    b=(A/'private/primary'/(e['name']+'.pdf')).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256'];primary+=1
extents=0
for line in (A/'private/primary/read-extents.jsonl').read_text().splitlines():
    e=json.loads(line);assert '/' not in e['name'];b=(A/'private/primary'/(e['name']+'.txt')).read_bytes()
    assert sha(b)==e['sha256'] and len(b)==e['total'] and 0<=e['start']<=e['stop']<=len(b);extents+=1
for name,intervals in coverage['primary_actual_display_unions'].items():
    b=(A/'private/primary'/(name+'.txt')).read_bytes();assert all(0<=lo<=hi<=len(b) for lo,hi in intervals)
assert coverage['original_history_body_sections_read']==[]
for name in ['original-navigation.json','symmetry-navigation.json','quotient-navigation.json']:assert read(A/'private'/name)['candidates']==[]
visual_names=['BR-page-4.png','BR-page-5.png','BR-page-15.png','BR-page-16.png','F96-section2-6.png','F96-section2-7.png','F96-section2-8.png']
for name in visual_names:assert ('private/primary/'+name) in before
controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as tmp:
    base=A/'controls/fixture';assert (base/'verify_packet.py').read_bytes()==(A/'verify_packet.py').read_bytes()
    ca={'FINAL':sha((base/'FINAL.md').read_bytes()),'MANIFEST':sha((base/'MANIFEST.json').read_bytes()),'REPORT':sha((base/'REPORT.md').read_bytes())}
    for case in ['intact','wrong-anchor','changed-bytes','extra-file','missing-file','file-mode','directory-mode']:
        dst=Path(tmp)/case;shutil.copytree(base,dst);aa=dict(ca);f=dst/'private/control.bin'
        if case=='wrong-anchor':aa['FINAL']='0'*64
        elif case=='changed-bytes':b=f.read_bytes();f.chmod(0o600);f.write_bytes(bytes([b[0]^1])+b[1:]);f.chmod(0o400)
        elif case=='extra-file':(dst/'extra.txt').write_text('extra\n')
        elif case=='missing-file':f.unlink()
        elif case=='file-mode':f.chmod(0o444)
        elif case=='directory-mode':(dst/'private').chmod(0o755)
        r=run(dst,aa);accepted=r.returncode==0;assert accepted==(case=='intact'),(case,r.stdout,r.stderr)
        controls.append({'case':case,'accepted':accepted,'expected':case=='intact'})
assert observe(A)==before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':json.loads(v.stdout),'selected_subdirectories':len(read(A/'MANIFEST.json')['directories']),'root_files':sum(e['type']=='file' for e in before.values()),'root_directories':sum(e['type']=='directory' for e in before.values()),'originals_bytes_modes_unchanged':True,'canonical_blobs':14,'full_text_read_record_bindings':texts,'textual_bytes_recorded':textbytes,'primary_pdf_bindings':primary,'primary_extent_identity_bindings':extents,'original_history_sections':0,'visual_record_identity_bindings':len(visual_names),'formal_navigation':read(A/'private/lean-338-access.json'),'copied_controls':controls,'limits':'Parent read complete DERIVATIONS, INTEGRATED-DERIVATIONS, READING-LIMITS, FINAL, REPORT, SESSION and verifier/control scripts. Underlying source/primary bodies and visual crops were identity-bound only; no semantic reading inherited. No history section admitted. Four boundary-overread types and primary/access/formal limits remain disclosed. Berndtsson-Rosay bibliographic year/volume differs between access log and READING-LIMITS; no silent correction or authoritative bibliographic resolution asserted. No mathematical grade or formal support.'}
for name,value in [('replay.json',out),('observed-root.json',before)]:
    p=P/name;p.write_text(json.dumps(value,indent=2)+'\n');p.chmod(0o600)
print(json.dumps(out,indent=2))
