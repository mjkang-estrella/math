#!/usr/bin/env python3
"""Read-only contribution intake, with parent-local namespace-adjusted tiny controls."""
from pathlib import Path
import datetime,hashlib,json,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]; R=C/'structural-r207-contribution-r1'; S=R/'packet'; A=C/'fresh-structural-discovery-r207'; D=A/'packet'
read=lambda p:json.loads(p.read_bytes()); sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'054f283a060b52565a1cf807ad030a72c3ba0020c354fc97f84c41f0d57e26b8','MANIFEST':'ff2e457d1e5be1dbc281056d04e3e6e5bca0862751bce2cbafad619cb3985fa5','REPORT':'089bfaeec058751091d6a4ad5faad060beb5ae329276938bcc92f4cc20adf64e'}
def observe(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        assert not p.is_symlink(); e={'type':'directory' if p.is_dir() else 'file','mode':format(stat.S_IMODE(p.stat().st_mode),'04o')}
        if p.is_file(): b=p.read_bytes(); e.update(bytes=len(b),sha256=sha(b))
        out['.' if p==root else p.relative_to(root).as_posix()]=e
    return out
def run(verifier,root,a):
    args=['python3','-I','-B',str(verifier),'--root',str(root)]
    for k in ['FINAL','MANIFEST','REPORT']: args.extend(['--'+k.lower()+'-sha256',a[k]])
    return subprocess.run(args,capture_output=True,text=True)
before=observe(R); author_before=observe(A); assert author_before==read(P/'observed-root.json')
verifier=S/'verify-review.py'; assert sha(verifier.read_bytes())=='9559695a098e05994e3fc72dba8d080027294d74cbd79ea2fdd59692a15650e0'
v=run(verifier,R,anchors); assert v.returncode==0,(v.stdout,v.stderr)
av=run(A/'verify-packet.py',A,read(P/'replay.json')['anchors']); assert av.returncode==0,(av.stdout,av.stderr)
m=read(R/'MANIFEST.json'); assert len(m['files'])==20 and len(m['directories'])==2
tb=(PROJECT/'sources/preprints-tree.json').read_bytes(); assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'; tree={e['path']:e for e in json.loads(tb)['tree']}
canon=read(S/'private/canonical-authentication.json'); assert canon['entries']==120 and len(canon['blobs'])==99
for e in canon['blobs']:
    b=(D/'private/canonical'/e['path']).read_bytes(); t=tree[e['path']]
    assert len(b)==e['bytes']==t['size'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==t['sha']
formal=read(S/'private/lean-verification.json')
for e in formal:
    p=D/'private/lean-331.md' if e['path']=='lean/docs/331.md' else D/'private/lean'/e['path']; b=p.read_bytes()
    assert len(b)==e['bytes'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']
extents=[json.loads(x) for x in (S/'private/read-extents.jsonl').read_text().splitlines()]
for e in extents:
    p=D/e['path']; assert p.is_relative_to(D); b=p.read_bytes(); assert sha(b)==e['sha256'] and 0<=e['start']<e['end']<=len(b)
access=[e for e in read(S/'private/probability-access.json') if 'file' in e]
for e in access:
    b=(S/'private'/e['file']).read_bytes(); assert len(b)==e['bytes'] and sha(b)==e['sha256']
pb=(S/'private/durrett2019.txt').read_bytes(); lines=pb.splitlines(keepends=True); pr=read(S/'private/probability-read-extents.json')
for e in pr:
    lo,hi=e['bytes_half_open']; a,b=e['lines_inclusive']; assert sha(pb)==e['sha256'] and pb[lo:hi]==b''.join(lines[a-1:b])
controls=[]
with tempfile.TemporaryDirectory(prefix='contribution-copied-controls-',dir=P) as tmp:
    tmp=Path(tmp); src=verifier.read_text(); old="EXCLUSIVE = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/structural-r207-contribution-r1')"
    assert src.count(old)==1; copied=tmp/'verify-review-copy.py'; copied.write_text(src.replace(old,'EXCLUSIVE = Path('+repr(str(tmp))+')'))
    base=R/'controls/baseline'; ca={k:sha((base/f).read_bytes()) for k,f in [('FINAL','packet/FINAL.md'),('MANIFEST','MANIFEST.json'),('REPORT','REPORT.md')]}
    for case in ['intact','wrong-anchor','changed-bytes','extra-file','changed-mode']:
        dst=tmp/case; shutil.copytree(base,dst); aa=dict(ca); f=dst/'packet/FROZEN.md'
        if case=='wrong-anchor': aa['FINAL']='0'*64
        elif case=='changed-bytes': b=f.read_bytes(); f.chmod(0o644); f.write_bytes(bytes([b[0]^1])+b[1:]); f.chmod(0o444)
        elif case=='extra-file': (dst/'packet').chmod(0o755); (dst/'packet/extra.txt').write_text('extra\n'); (dst/'packet').chmod(0o555)
        elif case=='changed-mode': f.chmod(0o644)
        q=run(copied,dst,aa); accepted=q.returncode==0; assert accepted==(case=='intact'),(case,q.stdout,q.stderr); controls.append({'case':case,'accepted':accepted,'expected':case=='intact'})
assert observe(R)==before and observe(A)==author_before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'review_sha256':sha((S/'REVIEW.md').read_bytes()),'verification':json.loads(v.stdout),'author_verification':json.loads(av.stdout),'root_files':sum(e['type']=='file' for e in before.values()),'root_directories':sum(e['type']=='directory' for e in before.values()),'review_originals_bytes_modes_unchanged':True,'all303_author_files80_directories_unchanged':True,'canonical_blobs':99,'formal_bindings':len(formal),'author_extent_metadata_bindings':len(extents),'new_probability_access_bindings':len(access),'new_probability_extent_bindings':len(pr),'render_integrity_only':2,'copied_controls':controls,'control_verifier_change':'Only EXCLUSIVE path constant changed in a temporary parent-local COPY so tiny copied controls can run in parent namespace; sealed verifier and originals untouched. Original sealed verifier separately passed on its actual review packet.','limits':'Parent read full review, working notes, session, FINAL, outside REPORT and source/access/read-limit record. Underlying source/primary/history/comparator bodies and renders were identity-bound only; no inherited semantic-reading or visual-inspection credit. Contribution remains conditional; no correctness grade or exhaustive literature/history claim.'}
for name,value in [('contribution-replay.json',out),('contribution-observed-root.json',before)]:
    p=P/name; p.write_text(json.dumps(value,indent=2)+'\n'); p.chmod(0o600)
print(json.dumps(out,indent=2))
