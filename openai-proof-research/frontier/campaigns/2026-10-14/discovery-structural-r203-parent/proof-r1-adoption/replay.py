#!/usr/bin/env python3
"""Read-only proof-review verification; tiny controls run only in parent-owned copies."""
from pathlib import Path
import datetime,hashlib,json,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent;C=P.parents[1];PROJECT=C.parents[2]
R=C/'structural-r203-proof-r1';A=C/'fresh-structural-discovery-r203';D=R/'packet/private'
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest();mode=lambda p:format(stat.S_IMODE(p.stat().st_mode),'04o')
anchors={'FINAL':'c2079bba1d3fabe5159ef8fdb329c34b14533873c387d7d1b9a44c6205d09ef9','MANIFEST':'89c19203a384a84ecffede68bf8747eb41a8a880287611effa7352b12d18656b','REPORT':'f509a0af7bbb4b6c5ebe22991d1139bf1c950f0afd404e80225361a91655bf14'}
def observe(root):
    out={'.':{'type':'directory','mode':mode(root)}}
    for p in sorted(root.rglob('*')):
        assert not p.is_symlink();e={'type':'directory' if p.is_dir() else 'file','mode':mode(p)}
        if p.is_file():b=p.read_bytes();e.update(bytes=len(b),sha256=sha(b))
        out[p.relative_to(root).as_posix()]=e
    return out
def command(root,a):
    return ['python3','-I','-B',str(R/'verify_packet.py'),'--packet',str(root/'packet'),'--manifest',str(root/'MANIFEST.json'),'--report',str(root/'REPORT.md'),'--final-sha256',a['FINAL'],'--manifest-sha256',a['MANIFEST'],'--report-sha256',a['REPORT']]
def run(argv):return subprocess.run(argv,capture_output=True,text=True)
before=observe(R);ab=observe(A);assert ab==read(P.parent/'observed-root.json')
v=run(command(R,anchors));assert v.returncode==0,(v.stdout,v.stderr)
m=read(R/'MANIFEST.json');files=[e for e in m['entries'] if e['type']=='file'];assert len(files)==27 and sum(e['size'] for e in files)==2351757
assert sha((R/'packet/REVIEW.md').read_bytes())=='5eeb2471971df763ea8cfd3cef7118b6dda9f681bea50fa7e0c72527c79044a6'
assert sha((R/'verify_packet.py').read_bytes())=='0142fb14c404c72a4d90338efba75acb99c66a16bbd897af8bbf7ae377084b54'
assert sha((R/'controls/results.json').read_bytes())=='7e8d119f291b43755a8bb1891f109ea2de18a69a1c0c9555d5501c6e9cc7af30'
assert (D/'author-FROZEN.md').read_bytes()==(A/'packet/FROZEN.md').read_bytes() and (D/'author-DERIVATION.md').read_bytes()==(A/'packet/DERIVATION.md').read_bytes()
rb=read(D/'author-before.json');assert rb==read(D/'author-after.json') and len(rb)==61
for e in rb:
    path=(PROJECT/e['path']).relative_to(A).as_posix();x=ab[path]
    assert x['type']==e['type'] and x['mode']==e['mode']
    if e['type']=='file':assert x['bytes']==e['size'] and x['sha256']==e['sha256']
assert read(D/'author-preservation.json')['unchanged'] and read(D/'author-verifier-replay.json')['returncode']==0
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree={e['path']:e for e in json.loads(tb)['tree']}
canon=read(D/'source-authentication.json')['blobs'];assert len(canon)==5
for e in canon:
    b=(A/'packet/private/upstream'/e['path']).read_bytes();t=tree[e['path']]
    assert len(b)==e['bytes']==t['size'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob_sha1']==t['sha']
formal=read(D/'formal-authentication.json');assert len(formal)==2
for e in formal:
    b=(A/'packet/private/upstream'/e['path']).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob_sha1']
log=read(D/'reading-ledger.json')
for e in log['direct']+log['author_semantic_full']+log['canonical_semantic']:
    path=e.get('path',e.get('selected_author_path'));lo,hi=e['bytes']
    with (PROJECT/path).open('rb') as stream:stream.seek(lo);b=stream.read(hi-lo)
    assert len(b)==hi-lo and sha(b)==e['sha256']
for e in log['history_semantic']:
    lo,hi=e['bytes']
    with (PROJECT/e['path']).open('rb') as stream:stream.seek(lo);b=stream.read(hi-lo)
    assert len(b)==hi-lo and sha(b)==e['sha256_selected']
primary_count=0
for e in log['primary_semantic']:
    if 'text_path' in e:
        b=(PROJECT/e['text_path']).read_bytes();lo,hi=e['bytes'];assert sha(b)==e['text_sha256'] and sha(b[lo:hi])==e['selected_sha256'];primary_count+=1
    elif 'path' in e:
        b=(PROJECT/e['path']).read_bytes();assert e['bytes']==[0,len(b)] and sha(b)==e['sha256'];primary_count+=1
assert primary_count==7
assert sha((D/'primary/Wenzel-1997v1.pdf').read_bytes())=='53ef6e9524d143f3758335bd5989e81bbfaf8e193433ea77a3833b471f6c19c1'
controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as tmp:
    dst=Path(tmp)/'fixture';shutil.copytree(R/'controls',dst);p=dst/'packet/review-opening.txt';original=p.read_bytes();original_mode=p.stat().st_mode & 0o777
    a={'FINAL':sha((dst/'packet/FINAL.md').read_bytes()),'MANIFEST':sha((dst/'MANIFEST.json').read_bytes()),'REPORT':sha((dst/'REPORT.md').read_bytes())}
    def check(name,argv,wanted):
        q=run(argv);ok=q.returncode==0;assert ok==wanted,(name,q.stdout,q.stderr);controls.append({'case':name,'accepted':ok,'expected':wanted})
    check('intact',command(dst,a),True)
    p.write_bytes(original+b'!');check('changed-bytes',command(dst,a),False);p.write_bytes(original)
    extra=dst/'packet/extra';extra.mkdir();check('extra-directory',command(dst,a),False);extra.rmdir()
    p.chmod(0o400);check('changed-mode',command(dst,a),False);p.chmod(original_mode)
    wrong=dict(a,MANIFEST='0'*64);check('wrong-anchor',command(dst,wrong),False)
    check('missing-report-anchor',command(dst,a)[:-2],False)
    check('restored',command(dst,a),True)
assert observe(R)==before and observe(A)==ab
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':json.loads(v.stdout),'root_files':sum(e['type']=='file' for e in before.values()),'root_directories':sum(e['type']=='directory' for e in before.values()),'author_files':50,'author_directories':14,'author_bytes_modes_unchanged':True,'review_bytes_modes_unchanged':True,'reviewer_author_baseline_files':50,'reviewer_author_baseline_directories':11,'canonical_blobs':5,'formal_bindings':2,'canonical_and_formal_reading_bindings':6,'primary_text_extent_bindings':7,'new_primary_pdf_bindings':1,'render_files_integrity_only':10,'history_spans':3,'direct_input_bindings':6,'copied_controls':controls,'frozen_statement_sha256':sha((A/'packet/FROZEN.md').read_bytes()),'author_proof_sha256':sha((A/'packet/DERIVATION.md').read_bytes()),'review_sha256':sha((R/'packet/REVIEW.md').read_bytes()),'limits':'Parent read full review, report, final handoff and reading/receipt metadata; no semantic reread of source/primary/history bodies or renders. Exact selected packet modes/bytes are bound by the manifest; outside verifier/control hashes bind through anchored REPORT, while outside modes/selection are only parent-baselined. Reviewer independently baselined 50 author files/11 selected directories, parent earlier baseline covers all50files/14directories.'}
for name,value in [('replay.json',out),('observed-root.json',before)]:
    p=P/name;p.write_text(json.dumps(value,indent=2)+'\n');p.chmod(0o600)
print(json.dumps(out,indent=2))
