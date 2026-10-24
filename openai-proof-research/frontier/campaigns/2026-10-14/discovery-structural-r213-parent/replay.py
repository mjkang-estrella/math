#!/usr/bin/env python3
"""Read-only artifact intake; this does not certify mathematics or inherit reading."""
from pathlib import Path
import datetime,hashlib,json,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2];A=C/'fresh-structural-discovery-r213';K=A/'packet'
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'455fe6dfd8c909c75c94c7c2d9c1d134f8ecdaa4056205416b5ebb28d85749d4','MANIFEST':'6250b940047f6e4d6c8f8363ed9793814006cb9c73f533d17da36fb862f33518','REPORT':'98c0ec37d321b820236238a71ef359854c43e1d1fe48c6605b8d5b465ee42c93'}
def observe(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        assert not p.is_symlink();e={'type':'directory' if p.is_dir() else 'file','mode':format(stat.S_IMODE(p.stat().st_mode),'04o')}
        if p.is_file():b=p.read_bytes();e.update(bytes=len(b),sha256=sha(b))
        out['.' if p==root else p.relative_to(root).as_posix()]=e
    return out
def run(root,report,a):
    args=['python3','-I','-B',str(A/'verify_packet.py'),'--packet',str(root),'--report',str(report)]
    for k in ['FINAL','MANIFEST','REPORT']:args.extend(['--'+k.lower()+'-sha256',a[k]])
    return subprocess.run(args,capture_output=True,text=True)
before=observe(A);vb=(A/'verify_packet.py').read_bytes();assert sha(vb)=='eae373aeace66072871d98eab1181c85d317e2d5526cad78ef9e5269e60a89bb' and vb==(K/'verify_packet.py').read_bytes()
v=run(K,A/'REPORT.md',anchors);assert v.returncode==0,(v.stdout,v.stderr)
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree={e['path']:e for e in json.loads(tb)['tree']};source=read(K/'private/authenticated.json');coverage=read(K/'private/source-coverage.json')['blobs'];assert len(source)==len(coverage)==32
allowed=['preprints/Generalized-Cartan-Hadamard-isoperimetry-and-Euclidean-equality-rigidity-September-23-2026/','preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/']
assert {e['path'] for e in source}=={p for p,e in tree.items() if e['type']=='blob' and any(p.startswith(s) for s in allowed)}
for e in source:
    b=(K/'private/pinned'/e['path']).read_bytes();t=tree[e['path']]
    assert len(b)==e['bytes']==t['size'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob_sha1']==t['sha']
texts=0;textbytes=0
for e in coverage:
    b=(K/'private/pinned'/e['path']).read_bytes();assert len(b)==e['bytes']
    if not e['fully_read']:
        assert e['path'].endswith(('/README.md','/build/glyph-mappings.tex','/paper.pdf'));continue
    assert e['intervals']==[[0,len(b)]] and not e['semantic_gaps'];texts+=1;textbytes+=len(b)
assert texts==26
for line in (K/'private/read-extents.jsonl').read_text().splitlines():
    e=json.loads(line);b=(K/e['path']).read_bytes();assert sha(b)==e['sha256'] and len(b)==e['file_bytes'] and 0<=e['byte_start']<=e['byte_end']<=len(b)
formal=0
for e in read(K/'private/formal-access.json'):
    b=(K/'private'/Path(e['path']).name).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob_sha1'];formal+=1
primary=0
access=read(K/'private/primary/access.json')+read(K/'private/primary/access-extra.json')+[read(K/'private/primary/access-AK.json'),dict(read(K/'private/primary/access-Almgren-recovery.json'),id='Almgren1986')]
for e in access:
    if 'failure' in e or e['id']=='MaggiSynopsis':continue
    b=(K/'private/primary'/(e['id']+'.pdf')).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256'];primary+=1
extents=0
for e in read(K/'private/selected-primary-recipe.json'):
    assert '/' not in e['id'];b=(A/'private/primary'/(e['id']+'.txt')).read_bytes()
    assert sha(b)==e['source_extraction_sha256'] and 0<=e['start']<=e['end']<=len(b)
    selected=b[e['start']:e['end']];assert sha(selected)==e['sha256'] and selected==(K/e['path']).read_bytes();extents+=1
history_names=['original-selection-r58-section1.txt','original-selection-r58-sections2-8.txt','original-selection-i286-7.txt','original-selection-i286-8.txt']
history_scopes=[('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r58/proof.md',631,2418),('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r58/proof.md',2418,17013),('frontier/iterations/i286-quantitative-cartan-hadamard.md',3773,5331),('frontier/iterations/i286-quantitative-cartan-hadamard.md',5331,7326)]
histories=0
for line,name,scope in zip((K/'private/original-reading.jsonl').read_text().splitlines(),history_names,history_scopes,strict=True):
    e=json.loads(line);assert (e['path'],e['start'],e['end'])==scope
    with (PROJECT/e['path']).open('rb') as f:f.seek(e['start']);b=f.read(e['end']-e['start'])
    assert b==(K/'private'/name).read_bytes();histories+=1
visual=0
for name,e in read(K/'private/primary/visual-reading.json').items():
    for page in e['pdf_pages_1based']:
        assert ('packet/private/primary/'+name+'-p'+str(page)+'.png') in before;visual+=1
controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as tmp:
    base=A/'controls';ca={'FINAL':sha((base/'packet/FINAL.md').read_bytes()),'MANIFEST':sha((base/'packet/MANIFEST.json').read_bytes()),'REPORT':sha((base/'REPORT.md').read_bytes())}
    for case in ['intact','wrong-anchor','changed-bytes','extra-file','missing-file','file-mode','directory-mode']:
        dst=Path(tmp)/case;shutil.copytree(base,dst);aa=dict(ca);f=dst/'packet/proof.txt'
        if case=='wrong-anchor':aa['FINAL']='0'*64
        elif case=='changed-bytes':b=f.read_bytes();f.chmod(0o644);f.write_bytes(bytes([b[0]^1])+b[1:]);f.chmod(0o444)
        elif case=='extra-file':(dst/'packet').chmod(0o755);(dst/'packet/extra.txt').write_text('extra\n');(dst/'packet/extra.txt').chmod(0o444);(dst/'packet').chmod(0o555)
        elif case=='missing-file':(dst/'packet').chmod(0o755);f.unlink();(dst/'packet').chmod(0o555)
        elif case=='file-mode':f.chmod(0o644)
        elif case=='directory-mode':(dst/'packet').chmod(0o755)
        r=run(dst/'packet',dst/'REPORT.md',aa);accepted=r.returncode==0;assert accepted==(case=='intact'),(case,r.stdout,r.stderr)
        controls.append({'case':case,'accepted':accepted,'expected':case=='intact'})
        for cp in dst.rglob('*'):
            if cp.is_dir():cp.chmod(0o755)
        dst.chmod(0o755)
assert observe(A)==before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':json.loads(v.stdout),'root_files':sum(e['type']=='file' for e in before.values()),'root_directories':sum(e['type']=='directory' for e in before.values()),'originals_bytes_modes_unchanged':True,'canonical_blobs':32,'operative_read_record_bindings':texts,'operative_bytes_recorded':textbytes,'primary_pdf_bindings':primary,'selected_primary_extent_identity_bindings':extents,'exact_original_history_span_bindings':histories,'visual_record_identity_bindings':visual,'formal_identity_bindings':formal,'formal_coverage':'Both comparator endpoints contain sorry per author reading; no proved endpoint coverage.','copied_controls':controls,'limits':'Parent read complete DERIVATIONS, RELATIVE-DERIVATION, STABILITY-REDUCTIONS, READING-LIMITS, FINAL, REPORT and verifier/control scripts. Underlying source/primary/history bodies and renders were identity-bound only, not semantically inherited. External editorial overread of 1193 bytes remains disclosed. No fresh parent primary retrieval, original-history clearance, mathematical grade or formal endpoint support.'}
for name,value in [('replay.json',out),('observed-root.json',before)]:
    p=P/name;p.write_text(json.dumps(value,indent=2)+'\n');p.chmod(0o600)
print(json.dumps(out,indent=2))
