#!/usr/bin/env python3
"""Read-only artifact intake; no mathematical certification."""
from pathlib import Path
import datetime,hashlib,json,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2];A=C/'fresh-structural-discovery-r211';K=A/'packet'
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'d5ee37bef3b494ae41773ceced770074c033c04545e451c2301fd28bc7c16d3e','MANIFEST':'fe146ff3bff80a60e6dbdea739578c528ab79605b86aa82fd6d10f3a5bb4a69d','REPORT':'f26ed2487194e7047c0b06ebdfc72e7106f55c2cfa5da9ccd1f796da36edc799'}
def observe(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        assert not p.is_symlink();e={'type':'directory' if p.is_dir() else 'file','mode':format(stat.S_IMODE(p.stat().st_mode),'04o')}
        if p.is_file():b=p.read_bytes();e.update(bytes=len(b),sha256=sha(b))
        out['.' if p==root else p.relative_to(root).as_posix()]=e
    return out
def run(root,a):
    args=['python3','-I','-B',str(A/'VERIFY.py'),'--root',str(root)]
    for k in ['FINAL','MANIFEST','REPORT']:args.extend(['--'+k.lower()+'-sha256',a[k]])
    return subprocess.run(args,capture_output=True,text=True)
before=observe(A);assert sha((A/'VERIFY.py').read_bytes())=='baab21374fc780397de59b5cca73f8f4db505c52d543c2e8fb623543a8b2fc76'
v=run(A,anchors);assert v.returncode==0,(v.stdout,v.stderr)
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree={e['path']:e for e in json.loads(tb)['tree']};source=read(K/'private/authenticated-blobs.json');coverage=read(K/'private/coverage.json')['canonical_blobs'];assert len(source)==len(coverage)==25
allowed=['preprints/An-integral-scalar-curvature-bound-for-real-simplicial-volume-October-5-2026/','preprints/Positive-scalar-curvature-forces-rational-inessentiality-September-23-2026/']
assert {e['path'] for e in source}=={p for p,e in tree.items() if e['type']=='blob' and any(p.startswith(s) for s in allowed)}
for e in source:
    b=(K/'private/canonical'/e['path']).read_bytes();t=tree[e['path']]
    assert len(b)==e['bytes']==t['size'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==t['sha']
texts=0;textbytes=0
for e in coverage:
    b=(K/'private/canonical'/e['path']).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256']
    if not e['path'].endswith('.pdf'):
        assert e['read_extents']==[[0,len(b)]] and e['semantic_read'];texts+=1;textbytes+=len(b)
assert texts==23 and textbytes==462414
primary=0
for e in read(K/'private/primary/retrieval.json')+read(K/'private/primary/retrieval-2.json'):
    if 'error' in e:continue
    b=(K/'private/primary'/(e['id']+'.pdf')).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256'];primary+=1
extents=0
for line in (K/'private/primary-read-extents.jsonl').read_text().splitlines():
    e=json.loads(line);assert e['file'].startswith('primary/') and '..' not in Path(e['file']).parts
    b=(K/'private'/e['file']).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256'] and 0<=e['start']<=e['end']<=len(b);extents+=1
controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as tmp:
    base=A/'controls';ca={'FINAL':sha((base/'FINAL.md').read_bytes()),'MANIFEST':sha((base/'MANIFEST.json').read_bytes()),'REPORT':sha((base/'outside/REPORT.md').read_bytes())}
    for case in ['intact','wrong-anchor','changed-bytes','extra-file','missing-file','file-mode','directory-mode']:
        dst=Path(tmp)/case;shutil.copytree(base,dst);aa=dict(ca);f=dst/'packet/private/guard-install.txt'
        if case=='wrong-anchor':aa['FINAL']='0'*64
        elif case=='changed-bytes':b=f.read_bytes();f.write_bytes(bytes([b[0]^1])+b[1:])
        elif case=='extra-file':(dst/'packet/extra.txt').write_text('extra\n')
        elif case=='missing-file':f.unlink()
        elif case=='file-mode':f.chmod(stat.S_IMODE(f.stat().st_mode)^0o100)
        elif case=='directory-mode':(dst/'packet').chmod(stat.S_IMODE((dst/'packet').stat().st_mode)^0o020)
        r=run(dst,aa);accepted=r.returncode==0;assert accepted==(case=='intact'),(case,r.stdout,r.stderr)
        controls.append({'case':case,'accepted':accepted,'expected':case=='intact'})
assert observe(A)==before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':json.loads(v.stdout),'root_files':sum(e['type']=='file' for e in before.values()),'root_directories':sum(e['type']=='directory' for e in before.values()),'originals_bytes_modes_unchanged':True,'canonical_blobs':25,'textual_read_record_bindings':texts,'textual_bytes_recorded':textbytes,'primary_pdf_bindings':primary,'primary_extent_identity_bindings':extents,'original_history_bodies_admitted':0,'formal_navigation':'HTTP404 reported; no comparator coverage','copied_controls':controls,'limits':'Parent read complete DERIVATIONS, RESEARCH, READING, FINAL, REPORT, OPERATIONS and verifier. Source/primary bodies and read extents were identity-bound only, not semantically inherited. No fresh parent primary retrieval, original-history clearance, mathematical grade or formal endpoint support.'}
for name,value in [('replay.json',out),('observed-root.json',before)]:
    p=P/name;p.write_text(json.dumps(value,indent=2)+'\n');p.chmod(0o600)
print(json.dumps(out,indent=2))
