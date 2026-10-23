#!/usr/bin/env python3
"""Read-only contribution-packet checks and copied tiny controls; no mathematical grade."""
from pathlib import Path
import datetime, hashlib, json, shutil, stat, subprocess, tempfile

P=Path(__file__).resolve().parent; C=P.parents[1]; PROJECT=C.parents[2]
R=C/'structural-r202-contribution-r1'; A=C/'fresh-structural-discovery-r202'
read=lambda p:json.loads(p.read_bytes())
sha=lambda b:hashlib.sha256(b).hexdigest()
mode=lambda p:format(stat.S_IMODE(p.stat().st_mode),'04o')
anchors={'FINAL.json':'d3b3d384aaca2cf0c16fcf270935e34a5f87a31599cbf26ac6c97896c36915f6','MANIFEST.json':'2dc78f9df9b7d8e0872624fcb70507fe6220612ec44e541a1c2ba008cc86f909','REPORT.md':'4d09d47eb7c4ad8fd829b026fb48cc9c40c5bbf7357e769ca66b8cfff4e08229'}

def observe(root):
    out={'.':{'mode':mode(root),'type':'directory'}}
    for p in sorted(root.rglob('*')):
        assert not p.is_symlink()
        e={'type':'directory' if p.is_dir() else 'file','mode':mode(p)}
        if p.is_file():
            b=p.read_bytes();e.update(bytes=len(b),sha256=sha(b))
        out[p.relative_to(root).as_posix()]=e
    return out

def verify(root, a):
    return subprocess.run(['python3','-I','-B',str(R/'verify_packet.py'),'--root',str(root),'--final-sha256',a['FINAL.json'],'--manifest-sha256',a['MANIFEST.json'],'--report-sha256',a['REPORT.md']],capture_output=True,text=True)

before=observe(R); author_before=observe(A)
assert author_before==read(P.parent/'observed-root.json')
for name,h in anchors.items():assert sha((R/name).read_bytes())==h
v=verify(R,anchors);assert v.returncode==0,(v.stdout,v.stderr)
m=read(R/'MANIFEST.json');f=read(R/'FINAL.json')
assert (len(m['files']),len(m['directories']))==(50,11)
assert f['contribution_verdict']=='TECHNICAL' and f['correctness_in_this_role']=='UNDISCHARGED'
assert f['essential_comparison_unresolved'] is False and f['seal_ordinal']==1
for name,h in f['author_anchors'].items():assert sha((A/name).read_bytes())==h
assert (R/'private/FROZEN-STATEMENT.md').read_bytes()==(A/'FROZEN-STATEMENT.md').read_bytes()
ab=read(R/'private/author-before.json');aa=read(R/'private/author-after.json')
assert ab==aa and len(ab)==123
for e in ab:
    now=author_before[e['path']]
    assert now==dict(type='file',**{k:e[k] for k in ['bytes','sha256','mode']})
av=read(R/'private/author-verification.json')
assert av['returncode']==0 and av['all_123_admitted_files_bytes_modes_unchanged']

tb=(PROJECT/'sources/preprints-tree.json').read_bytes()
assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree={e['path']:e for e in json.loads(tb)['tree']}
original={e['path']:e for e in read(A/'private/canonical-auth.json')}
canonical=read(R/'private/canonical-auth.json');assert len(canonical)==10
for e in canonical:
    o=original[e['path']];b=(A/o['local']).read_bytes();t=tree[e['path']]
    assert len(b)==e['bytes']==t['size'] and sha(b)==e['sha256']==o['sha256']
    assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==t['sha']
formal=read(R/'private/formal-auth.json');assert len(formal)==2
for e,name in zip(formal,['lean326.md','Cotype.lean']):
    b=(R/'private'/name).read_bytes();assert b==(A/'private'/name).read_bytes()
    assert sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']
    assert e['url'].startswith('https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/')
extents=[('frontier/iterations/i88-nonlinear-banach-discovery.md',1160,6225,'i88-nonlinear-banach-discovery-1160-6225.txt'),('frontier/iterations/i88-nonlinear-banach-discovery.md',30678,36024,'i88-nonlinear-banach-discovery-30678-36024.txt'),('frontier/iterations/i90-anchored-rank-approximation.md',26030,34763,'i90-anchored-rank-approximation-26030-34763.txt'),('sources/CONTENTS.md',552844,553766,'catalogue-excerpt.txt'),('frontier/NEW-TEN-2026-10-14.md',4801,6347,'acceptance-excerpt.txt')]
for name,lo,hi,copy in extents:
    with (PROJECT/name).open('rb') as stream:stream.seek(lo);b=stream.read(hi-lo)
    assert len(b)==hi-lo and b==(R/'private'/copy).read_bytes()
controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as tmp:
    for name,wanted in [('good',True),('changed-bytes',False),('changed-file-mode',False),('changed-directory-mode',False)]:
        dst=Path(tmp)/name;shutil.copytree(R/'private/controls'/name,dst)
        a=dict(line.split() for line in (dst/'ANCHORS.txt').read_text().splitlines())
        q=verify(dst,a);accepted=q.returncode==0
        assert accepted==wanted,(name,q.stdout,q.stderr)
        controls.append({'case':name,'accepted':accepted,'expected':wanted,'stdout':q.stdout.strip()})
assert observe(R)==before and observe(A)==author_before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':json.loads(v.stdout),'selected_bytes':sum(e['bytes'] for e in m['files']),'root_files':sum(e['type']=='file' for e in before.values()),'root_directories':sum(e['type']=='directory' for e in before.values()),'author_files':123,'author_directories':10,'author_bytes_modes_unchanged':True,'review_bytes_modes_unchanged':True,'canonical_bindings':10,'formal_bindings':2,'history_spans':3,'catalogue_acceptance_spans':2,'copied_controls':controls,'review_sha256':f['review_sha256'],'frozen_statement_sha256':f['author_anchors']['FROZEN-STATEMENT.md'],'author_proof_sha256':f['author_anchors']['AUTHOR-PROOF.md'],'limits':'Integrity checks are not semantic reading. Parent read review prose and reading/receipt metadata; source/primary/history bodies and eight new renders were not semantically reread. Author manifest omits directory/outside modes; independent parent baseline preserves all author modes. Own review manifest binds exact file/directory selection and modes, including outside-file modes.'}
for name,value in [('replay.json',out),('observed-root.json',before)]:
    p=P/name;p.write_text(json.dumps(value,indent=2)+'\n');p.chmod(0o600)
print(json.dumps(out,indent=2))
