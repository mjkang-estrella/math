#!/usr/bin/env python3
"""Read-only artifact intake; no mathematical certification."""
from pathlib import Path
import datetime,hashlib,json,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2];A=C/'fresh-structural-discovery-r212';K=A
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'83ba51300aa2eb382a18b251a3f1f7b348970b5271fae6bd0f45e2f75325b793','MANIFEST':'bb8bfa9aaae3e9ab39f2943ab2bf81d79dde94a78b53059f8f19c18d603f74c6','REPORT':'30dd3ac2d6d252b9a154a8e834ce34a4804c6d93de69a0c3bbc2186d962571ed'}
def observe(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        assert not p.is_symlink();e={'type':'directory' if p.is_dir() else 'file','mode':format(stat.S_IMODE(p.stat().st_mode),'04o')}
        if p.is_file():b=p.read_bytes();e.update(bytes=len(b),sha256=sha(b))
        out['.' if p==root else p.relative_to(root).as_posix()]=e
    return out
def run(root,a):
    args=['python3','-I','-B',str(A/'verify_packet.py'),'--root',str(root)]
    for k in ['FINAL','MANIFEST','REPORT']:args.extend(['--'+k.lower()+'-sha256',a[k]])
    return subprocess.run(args,capture_output=True,text=True)
before=observe(A);assert sha((A/'verify_packet.py').read_bytes())=='ecc6acfa11c793ef577aba9f514242e337896c409b5e6a92fe09281e5b77500c'
v=run(A,anchors);assert v.returncode==0,(v.stdout,v.stderr)
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree={e['path']:e for e in json.loads(tb)['tree']};source=read(K/'private/authentication.json');coverage=read(K/'private/source-coverage.json');assert len(source)==len(coverage)==38
allowed=['preprints/Spectral-scalar-curvature-and-uniform-Urysohn-width-October-5-2026/','preprints/Spectral-scalar-curvature-and-Urysohn-width-in-dimension-three-October-5-2026/','preprints/Positive-scalar-curvature-and-uniform-codimension-two-width-September-23-2026/']
assert {e['path'] for e in source}=={p for p,e in tree.items() if e['type']=='blob' and any(p.startswith(s) for s in allowed)}
for e in source:
    b=(K/'private/upstream'/e['path']).read_bytes();t=tree[e['path']]
    assert len(b)==e['bytes']==t['size'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==t['sha']
texts=0;textbytes=0
for e in coverage:
    if e['path'].endswith('.pdf'):continue
    b=(K/'private/upstream'/e['path']).read_bytes();assert len(b)==e['bytes']==e['covered_bytes'] and e['displayed_union']==[[0,len(b)]];texts+=1;textbytes+=len(b)
assert texts==35 and textbytes==540220
primary=0
for e in read(K/'private/primary-access.json')+[read(K/'private/moss-access.json')]:
    if 'failure' in e:continue
    b=(K/'private/primary'/(e['name']+'.pdf')).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256'];primary+=1
extents=0
for line in (K/'private/primary-read-extents.jsonl').read_text().splitlines():
    e=json.loads(line);assert '/' not in e['name']
    b=(K/'private/primary'/(e['name']+'.txt')).read_bytes();assert len(b)==e['total'] and sha(b)==e['sha256'] and 0<=e['start']<=e['end']<=len(b);extents+=1
histories=0
for e in read(K/'private/history-read-extents.json'):
    assert e['path']=='frontier/iterations/i14-sharp-spectral-width.md' and (e['start'],e['end']) in [(402,1673),(4139,5380),(5380,7471),(7471,9481),(9481,13013),(13013,16887),(16887,18869)]
    with (PROJECT/e['path']).open('rb') as f:f.seek(e['start']);b=f.read(e['end']-e['start'])
    assert sha(b)==e['sha256'] and b==(K/f"private/original-i14-{e['start']}-{e['end']}.md").read_bytes();histories+=1
assert histories==7
for name in ['moss-page-4.png','moss-page-7.png']:assert 'private/primary/'+name in before
controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as tmp:
    base=A/'private/seal-controls/fixture';ca={'FINAL':sha((base/'FINAL.md').read_bytes()),'MANIFEST':sha((base/'private/MANIFEST.json').read_bytes()),'REPORT':sha((base/'REPORT.md').read_bytes())}
    for case in ['intact','wrong-anchor','changed-bytes','extra-file','missing-file','file-mode','directory-mode']:
        dst=Path(tmp)/case;shutil.copytree(base,dst);aa=dict(ca);f=dst/'private/payload.txt'
        if case=='wrong-anchor':aa['FINAL']='0'*64
        elif case=='changed-bytes':b=f.read_bytes();f.write_bytes(bytes([b[0]^1])+b[1:])
        elif case=='extra-file':(dst/'extra.txt').write_text('extra\n')
        elif case=='missing-file':f.unlink()
        elif case=='file-mode':f.chmod(stat.S_IMODE(f.stat().st_mode)^0o100)
        elif case=='directory-mode':(dst/'private').chmod(stat.S_IMODE((dst/'private').stat().st_mode)^0o020)
        r=run(dst,aa);accepted=r.returncode==0;assert accepted==(case=='intact'),(case,r.stdout,r.stderr)
        controls.append({'case':case,'accepted':accepted,'expected':case=='intact'})
assert observe(A)==before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':json.loads(v.stdout),'root_files':sum(e['type']=='file' for e in before.values()),'root_directories':sum(e['type']=='directory' for e in before.values()),'originals_bytes_modes_unchanged':True,'canonical_blobs':38,'textual_read_record_bindings':texts,'textual_bytes_recorded':textbytes,'primary_pdf_bindings':primary,'primary_extent_identity_bindings':extents,'exact_original_history_span_bindings':histories,'visual_record_identity_bindings':2,'formal_navigation':'HTTP404 reported; no comparator coverage','copied_controls':controls,'limits':'Parent read complete CONFORMAL-COMPOSITION, DERIVATIONS, READING, FINAL, REPORT, SESSION and verifier. Source/primary/history bodies and renders were identity-bound only, not semantically inherited. External wrapper overread remains disclosed. No fresh parent primary retrieval, original-history clearance, mathematical grade or formal endpoint support.'}
for name,value in [('replay.json',out),('observed-root.json',before)]:
    p=P/name;p.write_text(json.dumps(value,indent=2)+'\n');p.chmod(0o600)
print(json.dumps(out,indent=2))
