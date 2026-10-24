#!/usr/bin/env python3
"""Read-only correctness intake; controls use tiny parent-local copies only."""
from pathlib import Path
import datetime,hashlib,json,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]
R=C/'structural-r207-proof-r1'; S=R/'packet'; A=C/'fresh-structural-discovery-r207'; D=A/'packet'; Q=C/'structural-r207-contribution-r1'
read=lambda p:json.loads(p.read_bytes()); sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'9ebc00b34549b934e69628ea2987af4daa0cf1bd77edb2a1924559da404ac3cc','MANIFEST':'0c7affc09c9b54f1d3a00e8dd1d9d7498540516a812e1fd897b1cab8fb1ccafe','REPORT':'62b0dc8dee2a849e2845d6aa52b09abde23469d1c939e0ca9db554d37582b381'}
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
before=observe(R); ab=observe(A); qb=observe(Q)
assert ab==read(P/'observed-root.json') and qb==read(P/'contribution-observed-root.json')
verifier=R/'verify-packet.py'; assert sha(verifier.read_bytes())=='358f4b2d0fc6d8decb3ad88d166befd14e2c5903e8dd5996fa58a7afee5e66c0'
v=run(verifier,R,anchors); assert v.returncode==0,(v.stdout,v.stderr)
av=run(A/'verify-packet.py',A,read(P/'replay.json')['anchors']); assert av.returncode==0,(av.stdout,av.stderr)
m=read(R/'MANIFEST.json'); assert len(m['files'])==26 and len(m['directories'])==7
tb=(PROJECT/'sources/preprints-tree.json').read_bytes(); assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'; tree={e['path']:e for e in json.loads(tb)['tree']}
canon=read(S/'private/SOURCE-AUTHENTICATION.json'); assert canon['entries']==120 and len(canon['blobs'])==99
for e in canon['blobs']:
    b=(D/'private/canonical'/e['path']).read_bytes(); t=tree[e['path']]
    assert len(b)==e['bytes']==t['size'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==t['sha']
formal=read(S/'private/LEAN-AUTHENTICATION.json')
for e in formal:
    p=D/'private/lean-331.md' if e['path']=='lean/docs/331.md' else D/'private/lean'/e['path']; b=p.read_bytes()
    assert b==(S/'private/lean-pin'/e['path']).read_bytes()
    assert len(b)==e['bytes'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']
logs=[json.loads(x) for x in (S/'private/read-log.jsonl').read_text().splitlines()]; bound=0; unhashed=0
for e in logs:
    p=D/e['path']; assert p.is_relative_to(D); b=p.read_bytes()
    if 'sha256' in e:
        assert sha(b)==e['sha256'] and len(b)==e['total_bytes']; lo,hi=e['bytes']; assert 0<=lo<hi<=len(b)
        if 'lines' in e:
            a,z=e['lines']; assert b[lo:hi]==b''.join(b.splitlines(keepends=True)[a-1:z])
        bound+=1
    else:
        a,z=e['lines']; assert 1<=a<=z<=len(b.splitlines()); unhashed+=1
for n in ['FROZEN.md','AUTHOR-PROOF.md']: assert (S/'private/submission'/n).read_bytes()==(D/n).read_bytes()
controls=[]
with tempfile.TemporaryDirectory(prefix='proof-copied-controls-',dir=P) as tmp:
    tmp=Path(tmp); base=R/'controls/baseline'; ca={k:sha((base/f).read_bytes()) for k,f in [('FINAL','packet/FINAL.md'),('MANIFEST','MANIFEST.json'),('REPORT','REPORT.md')]}
    for case in ['intact','wrong-anchor','changed-bytes','extra-file','missing-file','file-mode','directory-mode']:
        dst=tmp/case; shutil.copytree(base,dst); aa=dict(ca); f=dst/'packet/FROZEN.md'
        if case=='wrong-anchor': aa['MANIFEST']='0'*64
        elif case=='changed-bytes': b=f.read_bytes(); f.chmod(0o644); f.write_bytes(bytes([b[0]^1])+b[1:]); f.chmod(0o444)
        elif case in ['extra-file','missing-file']:
            (dst/'packet').chmod(0o755)
            if case=='extra-file': (dst/'packet/extra.txt').write_text('extra\n')
            else: f.unlink()
            (dst/'packet').chmod(0o555)
        elif case=='file-mode': f.chmod(0o644)
        elif case=='directory-mode': (dst/'packet').chmod(0o755)
        q=run(verifier,dst,aa); accepted=q.returncode==0; assert accepted==(case=='intact'),(case,q.stdout,q.stderr)
        controls.append({'case':case,'accepted':accepted,'expected':case=='intact'})
assert observe(R)==before and observe(A)==ab and observe(Q)==qb
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'review_sha256':sha((S/'REVIEW.md').read_bytes()),'verification':json.loads(v.stdout),'author_verification':json.loads(av.stdout),'root_files':sum(e['type']=='file' for e in before.values()),'root_directories':sum(e['type']=='directory' for e in before.values()),'review_originals_bytes_modes_unchanged':True,'all303_author_files80_directories_unchanged':True,'contribution44files12directories_unchanged':True,'canonical_blobs':99,'formal_bindings':len(formal),'hashed_extent_metadata_bindings':bound,'unhashed_line_range_bindings':unhashed,'copied_controls':controls,'control_verifier_change':None,'limits':'Parent read the full review, independent mathematical notes, complete reading record, FINAL and outside REPORT. Underlying source, primary, original-history and comparator bodies were identity-bound only; no inherited semantic reading, visual inspection or formal proof credit. Navigation extracts were not read as proof. No exhaustive literature/history clearance.'}
for name,value in [('proof-replay.json',out),('proof-observed-root.json',before)]:
    p=P/name; p.write_text(json.dumps(value,indent=2)+'\n'); p.chmod(0o600)
print(json.dumps(out,indent=2))
