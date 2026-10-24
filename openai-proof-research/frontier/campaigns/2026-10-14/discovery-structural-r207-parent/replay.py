#!/usr/bin/env python3
"""Read-only author identity replay; tiny copied controls remain parent-local."""
from pathlib import Path
import datetime,hashlib,json,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]; R=C/'fresh-structural-discovery-r207'; S=R/'packet'; D=S/'private'
read=lambda p:json.loads(p.read_bytes()); sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'3143ca3bd3708fdfda18e3d38b74bd77d5add05b55d01a62ad91888039e21c5f','MANIFEST':'4be53433bbd39ef3805d1b6b3424db92809a4053836fc81076dee2a850e36e23','REPORT':'e457e25176f7a4f58ada7cd504abf9b21c1cb8377fd7e92394b5d10d9355af02'}
frozen='7e9597aa5af080257a8a1f88e7a99a3bc41d3c0668fcf3e109076c4097d1d4e2'
def observe(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        assert not p.is_symlink(); e={'type':'directory' if p.is_dir() else 'file','mode':format(stat.S_IMODE(p.stat().st_mode),'04o')}
        if p.is_file(): b=p.read_bytes(); e.update(bytes=len(b),sha256=sha(b))
        out['.' if p==root else p.relative_to(root).as_posix()]=e
    return out
def run(root,a):
    args=['python3','-I','-B',str(R/'verify-packet.py'),'--root',str(root)]
    for k in ['FINAL','MANIFEST','REPORT']: args.extend(['--'+k.lower()+'-sha256',a[k]])
    return subprocess.run(args,capture_output=True,text=True)
before=observe(R)
assert sha((R/'verify-packet.py').read_bytes())=='358f4b2d0fc6d8decb3ad88d166befd14e2c5903e8dd5996fa58a7afee5e66c0'
assert sha((S/'FROZEN.md').read_bytes())==sha((R/'FROZEN.md').read_bytes())==frozen
v=run(R,anchors); assert v.returncode==0,(v.stdout,v.stderr)
m=read(R/'MANIFEST.json'); assert len(m['files'])==146 and len(m['directories'])==39
tb=(PROJECT/'sources/preprints-tree.json').read_bytes(); assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree={e['path']:e for e in json.loads(tb)['tree']}; canonical=read(D/'authentication.json'); assert len(canonical)==99
for e in canonical:
    b=(D/'canonical'/e['path']).read_bytes(); t=tree[e['path']]
    assert len(b)==e['bytes']==t['size'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==t['sha']
formal=read(D/'lean-authentication.json'); assert len(formal)==8
for e in formal:
    p=D/'lean-331.md' if e['path']=='lean/docs/331.md' else D/'lean'/e['path']; b=p.read_bytes()
    assert len(b)==e['bytes'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']
for path,lo,hi,h in [('sources/CONTENTS.md',557394,562805,'bdb798a73ac94eb7b6327bb288976a08cd393b5795b2bc58e1760134439ce634'),('frontier/NEW-TEN-2026-10-14.md',4801,6347,'f147924a01d36cce7ad5ee13bad6ed9ed9109f3bf4b5c2386fc318aae1330984')]:
    with (PROJECT/path).open('rb') as f: f.seek(lo); b=f.read(hi-lo)
    assert len(b)==hi-lo and sha(b)==h
history=0
for i,e in enumerate(read(D/'history-sections.json'),1):
    if i==1: continue  # Disclosed administrative false admission is not re-read.
    assert e['path']=='frontier/iterations/i88-nonlinear-banach-discovery.md'
    with (PROJECT/e['path']).open('rb') as f: f.seek(e['start']); b=f.read(e['end']-e['start'])
    assert b==(D/'history-selected'/f'section-{i}.txt').read_bytes(); history+=1
primary=[e for e in read(D/'primary/access.json') if e.get('pdf')]
for e in primary:
    b=(D/'primary'/(e['id']+'.pdf')).read_bytes(); assert len(b)==e['bytes'] and sha(b)==e['sha256']
extents=[json.loads(s) for s in (D/'read-extents.jsonl').read_text().splitlines()]; checked=0
for e in extents:
    path=e['path']
    if path.startswith('preprints/'): p=D/'canonical'/path
    elif path.startswith('frontier/campaigns/2026-10-14/fresh-structural-discovery-r207/private/'):
        p=D/path.split('/private/',1)[1]
    else: continue
    b=p.read_bytes(); assert sha(b)==e['sha256'] and 0<=e['start']<e['end']<=len(b); checked+=1
controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as tmp:
    base=R/'controls'; a={k:sha((base/f).read_bytes()) for k,f in [('FINAL','packet/FINAL.md'),('MANIFEST','MANIFEST.json'),('REPORT','REPORT.md')]}
    for case in ['intact','changed-bytes','changed-mode','extra-file','wrong-anchor','intact-again']:
        dst=Path(tmp)/case; shutil.copytree(base,dst); f=dst/'packet/FROZEN.md'; aa=dict(a)
        if case=='changed-bytes': b=f.read_bytes(); f.chmod(0o644); f.write_bytes(bytes([b[0]^1])+b[1:]); f.chmod(0o444)
        elif case=='changed-mode': f.chmod(0o644)
        elif case=='extra-file': (dst/'packet').chmod(0o755); (dst/'packet/extra.txt').write_text('extra\n'); (dst/'packet').chmod(0o555)
        elif case=='wrong-anchor': aa['MANIFEST']='0'*64
        q=run(dst,aa); accepted=q.returncode==0; expected=case in ['intact','intact-again']; assert accepted==expected,(case,q.stdout,q.stderr)
        controls.append({'case':case,'accepted':accepted,'expected':expected})
assert observe(R)==before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'frozen_sha256':frozen,'proof_sha256':sha((S/'AUTHOR-PROOF.md').read_bytes()),'verification':json.loads(v.stdout),'root_files':sum(e['type']=='file' for e in before.values()),'root_directories':sum(e['type']=='directory' for e in before.values()),'originals_bytes_modes_unchanged':True,'canonical_blobs':99,'formal_bindings':len(formal),'primary_pdf_bindings':len(primary),'extent_metadata_bindings':checked,'history_exact_spans':history,'administrative_history_selection_not_reread':True,'direct_input_spans':2,'copied_controls':controls,'limits':'Parent read frozen statement and complete original author research/proof/checks/reading prose, FINAL and REPORT. Underlying source/primary/history and formal bodies were identity-bound only, with no inherited semantic-reading credit. Formal bindings rely on supplied pinned metadata rather than independent network retrieval. Exact selected packet has146 files/39 directories. No mathematical grade or history/literature exhaustion claim.'}
for name,value in [('replay.json',out),('observed-root.json',before)]:
    p=P/name; p.write_text(json.dumps(value,indent=2)+'\n'); p.chmod(0o600)
print(json.dumps(out,indent=2))
