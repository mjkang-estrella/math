#!/usr/bin/env python3
"""Read-only Structural206 identity checks; copied controls live in parent root."""
from pathlib import Path
import datetime,hashlib,json,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]; R=C/'fresh-structural-discovery-r206'; S=R/'selected'
read=lambda p:json.loads(p.read_bytes()); sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'1751f90c071bfb2e04d352b307240b91febbbf8d959a8935460c62505a174cf1','MANIFEST':'f0a2c5a4fe7c6dec72112f7b02cf71f458f04ed07b8235c578510ca045717db6','REPORT':'87ac0f08ae17c4682f9ddcd7fbd57c8f9f7ee5150aa5d83862a191735e749a96'}
def observe(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        assert not p.is_symlink(); e={'type':'directory' if p.is_dir() else 'file','mode':format(stat.S_IMODE(p.stat().st_mode),'04o')}
        if p.is_file(): b=p.read_bytes(); e.update(bytes=len(b),sha256=sha(b))
        out['.' if p==root else p.relative_to(root).as_posix()]=e
    return out
def run(root,a):
    args=['python3','-I','-B',str(R/'verify_packet.py'),'--packet',str(root/'selected'),'--manifest',str(root/'MANIFEST.json'),'--report',str(root/'REPORT.md')]
    for k in ['FINAL','MANIFEST','REPORT']: args.extend(['--'+k.lower()+'-sha',a[k]])
    return subprocess.run(args,capture_output=True,text=True)
before=observe(R); v=run(R,anchors); assert v.returncode==0,(v.stdout,v.stderr)
m=read(R/'MANIFEST.json'); assert len(m['files'])==80 and len(m['directories'])==8
assert (R/'verify_packet.py').read_bytes()==(S/'verify_packet.py').read_bytes()
tb=(PROJECT/'sources/preprints-tree.json').read_bytes(); assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree={e['path']:e for e in json.loads(tb)['tree']}
canonical=[e for e in read(S/'private-source/authentication.json') if e['path'].startswith('preprints/')]; assert len(canonical)==11
for e in canonical:
    b=(S/e['local']).read_bytes(); t=tree[e['path']]
    assert len(b)==e['bytes']==t['size'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==t['sha']
for e in read(S/'private-source/lean-authentication.json'):
    local='lean-330.md' if e['path']=='lean/docs/330.md' else Path(e['path']).name
    b=(S/'private-source'/local).read_bytes()
    assert len(b)==e['bytes'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==e['metadata_sha']
direct=read(S/'private-metadata/direct-inputs.json')
for key in ['catalogue','acceptance']:
    e=direct[key]; lo,hi=e['byte_extent']
    with (PROJECT/e['path']).open('rb') as f: f.seek(lo); b=f.read(hi-lo)
    assert len(b)==e['bytes'] and sha(b)==e['sha256']
history=0
for name in ['read-extents-1.json','read-extents-2.json','read-extents-3.json']:
    rows=read(S/'private-history'/name); rows=rows if isinstance(rows,list) else [rows]
    for e in rows:
        assert e['path'] in ['frontier/iterations/i88-nonlinear-banach-discovery.md','frontier/iterations/i90-anchored-rank-approximation.md']
        lo,hi=e.get('byte_extent',e.get('bytes'))
        with (PROJECT/e['path']).open('rb') as f: f.seek(lo); b=f.read(hi-lo)
        assert len(b)==hi-lo and sha(b)==e['selection_sha256']; history+=1
primary=read(S/'private-primary/acquisition.json')
for name,record in [('Brudnyi07','Brudnyi07-acquisition.json'),('Godefroy24','Godefroy24-access.json')]:
    e=read(S/'private-primary'/record); e['name']=name; primary.append(e)
for e in primary:
    b=(S/'private-primary'/(e['name']+'.pdf')).read_bytes(); assert len(b)==e['bytes'] and sha(b)==e['sha256']
extents=read(S/'private-primary/semantic-read-extents.json')
for e in extents:
    b=(S/e['file']).read_bytes(); lo,hi=e['utf8_bytes']; selection=(S/e['selection_file']).read_bytes()
    assert sha(b)==e['sha256'] and b[lo:hi]==selection and sha(selection)==e['selection_sha256']
controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as tmp:
    base=R/'tiny-controls/baseline'; a={k:sha((base/f).read_bytes()) for k,f in [('FINAL','selected/FINAL.md'),('MANIFEST','MANIFEST.json'),('REPORT','REPORT.md')]}
    for case in ['unchanged','changed-bytes','changed-mode','missing-file','extra-file','wrong-anchor']:
        dst=Path(tmp)/case; shutil.copytree(base,dst); f=dst/'selected/FINAL.md'; aa=dict(a)
        if case=='changed-bytes': b=f.read_bytes(); f.chmod(0o600); f.write_bytes(b+b'!'); f.chmod(0o400)
        elif case=='changed-mode': f.chmod(0o600)
        elif case in ['missing-file','extra-file']:
            (dst/'selected').chmod(0o700)
            if case=='missing-file': f.unlink()
            else: (dst/'selected/extra.txt').write_text('extra\n')
            (dst/'selected').chmod(0o500)
        elif case=='wrong-anchor': aa['FINAL']='0'*64
        q=run(dst,aa); accepted=q.returncode==0; assert accepted==(case=='unchanged'),(case,q.stdout,q.stderr)
        controls.append({'case':case,'accepted':accepted,'expected':case=='unchanged'})
assert observe(R)==before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':json.loads(v.stdout),'root_files':sum(e['type']=='file' for e in before.values()),'root_directories':sum(e['type']=='directory' for e in before.values()),'originals_bytes_modes_unchanged':True,'canonical_blobs':11,'formal_bindings':3,'primary_pdf_bindings':len(primary),'primary_extent_records':len(extents),'history_exact_spans':history,'direct_input_spans':2,'copied_controls':controls,'mathematics_sha256':sha((S/'mathematics.md').read_bytes()),'derivations_sha256':sha((S/'derivations.md').read_bytes()),'reading_sha256':sha((S/'READING.md').read_bytes()),'verifier_sha256':sha((R/'verify_packet.py').read_bytes()),'limits':'Parent read original research prose, FINAL, REPORT and reading/access metadata. Source, primary, history bodies and render bound for identity only, with no inherited semantic-reading credit. Canonical blobs tied to complete pinned tree; formal files tied to supplied pinned metadata, not independent network retrieval. No mathematical grade or exhaustive novelty/isolation claim.'}
for name,value in [('replay.json',out),('observed-root.json',before)]:
    p=P/name; p.write_text(json.dumps(value,indent=2)+'\n'); p.chmod(0o600)
print(json.dumps(out,indent=2))
