#!/usr/bin/env python3
"""Read-only artifact intake; no mathematical grade or inherited semantic reading."""
from pathlib import Path
import collections,datetime,hashlib,json,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2];A=C/'fresh-structural-discovery-r217'
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'0b5e19b012ab2a779eb1ba0901de3ef2c6e58dd9263b4e65b2910ce5459cc33b','MANIFEST':'130a811bdfef0f82e76add026a59e0b7082a8814f0a24a6883dec0ddb5439f93','REPORT':'f40e59a267ba73764571b2cb376d58319c2b69f910ddbf54c96f726b1e907453'}
def observe(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        assert not p.is_symlink();e={'type':'directory' if p.is_dir() else 'file','mode':format(stat.S_IMODE(p.stat().st_mode),'04o')}
        if p.is_file():b=p.read_bytes();e.update(bytes=len(b),sha256=sha(b))
        out['.' if p==root else p.relative_to(root).as_posix()]=e
    return out
def run(root,a):
    args=['python3','-I','-B',str(A/'verify_packet.py'),'--root',str(root)]
    for k in anchors:args.extend(['--'+k.lower()+'-sha256',a[k]])
    return subprocess.run(args,capture_output=True,text=True)
before=observe(A);assert sha((A/'verify_packet.py').read_bytes())=='87d5981a0f07a4111e8b7e50dfd95ae1cc467e2d72f2d3882e0c25b9450098aa'
v=run(A,anchors);assert v.returncode==0,(v.stdout,v.stderr)
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree={e['path']:e for e in json.loads(tb)['tree']};source=read(A/'private/source-authentication.json');companion=read(A/'private/companion-authentication.json');assert len(source)==34 and len(companion)==25
for e in source+companion:
    p=A/'private'/e['path'];b=p.read_bytes();t=tree[e['path']]
    assert len(b)==e['bytes']==t['size'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==t['sha']
S=A/'private/preprints/Deforming-hypersymplectic-four-manifolds-to-hyperkahler-triples-'
T=A/'private/preprints/Taming-implies-compatibility-on-four-manifolds-'
so=Path(str(S)+'October-7-2026');ss=Path(str(S)+'September-23-2026');co=Path(str(T)+'October-6-2026');cs=Path(str(T)+'September-23-2026')
for e in read(A/'private/version-equality.json'):
    x=(so/e['suffix']).read_bytes();y=(ss/e['suffix']).read_bytes();assert len(x)==e['october_bytes'] and len(y)==e['september_bytes'] and (x==y)==e['actual_byte_equal']
for e in read(A/'private/companion-equality.json'):
    if e.get('september')=='absent':assert not (cs/e['path']).exists();continue
    x=(co/e['path']).read_bytes();y=(cs/e['path']).read_bytes();assert sha(x)==e['oct_sha256'] and sha(y)==e['sep_sha256'] and (x==y)==e['identical']
maps=read(A/'private/version-operative-map.json');groups=collections.defaultdict(list)
for e in maps:groups[e['file']].append(e)
for name,es in groups.items():
    x=(so/name).read_bytes();y=(ss/name).read_bytes();xo=yo=0
    for e in es:
        lo,hi=e['october_bytes'];a,b=e['september_bytes'];assert lo==xo and a==yo and hi<=len(x) and b<=len(y)
        if e['op']=='equal':assert x[lo:hi]==y[a:b]
        xo,yo=hi,b
    assert xo==len(x) and yo==len(y)
companion_blocks=0
for e in read(A/'private/companion-operative-map.json'):
    x=(co/e['path']).read_bytes();y=(cs/e['path']).read_bytes();xo=yo=0
    for z in e['blocks']:
        lo,hi=z['october'];a,b=z['september'];assert lo==xo and a==yo and hi<=len(x) and b<=len(y)
        assert sha(x[lo:hi])==z['oct_sha256'] and sha(y[a:b])==z['sep_sha256']
        if z['op']=='equal':assert x[lo:hi]==y[a:b]
        xo,yo=hi,b;companion_blocks+=1
    assert xo==len(x) and yo==len(y)
logs=[json.loads(s) for s in (A/'private/semantic-reads.jsonl').read_text().splitlines()]
for e in logs:
    p=A/e['path'];assert p.is_relative_to(A);b=p.read_bytes();lo,hi=e['bytes'];assert 0<=lo<=hi<=len(b) and sha(b[lo:hi])==e['sha256']
pdfs=0
for e in read(A/'private/primary-access.json')+read(A/'private/late-primary-access.json'):
    b=(A/'private/primary'/(e['name']+'.pdf')).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256'];pdfs+=1
extents=0
for e in read(A/'private/primary-selected-extents.json'):
    b=(A/'private/primary'/(e['name']+'.txt')).read_bytes();assert sha(b)==e['file_sha256']
    for z in e['selected_math']:
        lo,hi=z['bytes'];assert 0<=lo<=hi<=len(b) and sha(b[lo:hi])==z['sha256'];extents+=1
e=read(A/'private/history-selection.json')['selected'];assert e['path']=='frontier/iterations/i80-geometric-flows-computation-discovery.md' and e['bytes']==[5249,7726]
with (PROJECT/e['path']).open('rb') as f:f.seek(5249);b=f.read(7726-5249)
assert sha(b)==e['sha256'] and b==(A/'private/original-i80-G.txt').read_bytes()
controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as tmp:
    base=A/'controls/tiny-copy';ca={k:sha((base/(k+('.json' if k=='MANIFEST' else '.md'))).read_bytes()) for k in anchors}
    for case in ['intact','wrong-anchor','changed-bytes','extra-file','missing-file','file-mode','directory-mode']:
        dst=Path(tmp)/case;shutil.copytree(base,dst);a=dict(ca);f=dst/'payload.txt'
        if case=='wrong-anchor':a['FINAL']='0'*64
        elif case=='changed-bytes':b=f.read_bytes();f.write_bytes(bytes([b[0]^1])+b[1:])
        elif case=='extra-file':(dst/'extra.txt').write_text('extra\n')
        elif case=='missing-file':f.unlink()
        elif case=='file-mode':f.chmod(0o644)
        elif case=='directory-mode':dst.chmod(0o755)
        q=run(dst,a);ok=q.returncode==0;assert ok==(case=='intact'),(case,q.stdout,q.stderr);controls.append({'case':case,'accepted':ok,'expected':case=='intact'})
assert observe(A)==before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':json.loads(v.stdout),'root_files':sum(e['type']=='file' for e in before.values()),'root_directories':sum(e['type']=='directory' for e in before.values()),'originals_bytes_modes_unchanged':True,'source_canonical_blobs':34,'companion_canonical_blobs':25,'source_version_map_blocks':len(maps),'companion_version_map_blocks':companion_blocks,'logged_extent_identity_bindings':len(logs),'primary_pdf_bindings':pdfs,'corrected_primary_math_extent_bindings':extents,'exact_original_history_span_bindings':1,'formal_navigation':read(A/'private/lean-access.json'),'copied_controls':controls,'limits':'Parent read full MATH, FINAL, REPORT, SESSION, private/READING and verifier. Underlying source, primary and original-history bodies identity-bound only without inherited semantic reading. The read-request log includes actual exposures/offset mistakes and is not treated as a blanket coverage certificate; corrected primary mathematical selections, version comparison maps, late reads, truncation recoveries and unread intermediates remain disclosed. No exhaustive history clearance, mathematical grade or formal support.'}
for name,value in [('replay.json',out),('observed-root.json',before)]:
    p=P/name;p.write_text(json.dumps(value,indent=2)+'\n');p.chmod(0o600)
print(json.dumps(out,indent=2))
