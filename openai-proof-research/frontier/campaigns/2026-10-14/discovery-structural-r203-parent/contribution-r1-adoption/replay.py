#!/usr/bin/env python3
"""Read-only contribution packet verification; controls mutate parent-owned copies only."""
from pathlib import Path
import datetime,hashlib,json,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent;C=P.parents[1];PROJECT=C.parents[2]
R=C/'structural-r203-contribution-r1';A=C/'fresh-structural-discovery-r203';D=R/'packet/private'
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'9eca1195fa12598d7e8dafdf77ad7a64110cab00b13d728e0a867aed8c5f40fb','MANIFEST':'90043a3a2e1956d0678c68b7982c5fc71734975d3b58a127597f98af25a1826c','REPORT':'ab9f93a3f4c15cc865788fa4318c76c133b6d0c27891dccc74eae378a969eb37'}
def observe(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        assert not p.is_symlink();e={'type':'directory' if p.is_dir() else 'file','mode':format(stat.S_IMODE(p.stat().st_mode),'04o')}
        if p.is_file():b=p.read_bytes();e.update(bytes=len(b),sha256=sha(b))
        out['.' if p==root else p.relative_to(root).as_posix()]=e
    return out
def command(root,a):
    return ['python3','-I','-B',str(R/'verify_packet.py'),'--packet',str(root/'packet'),'--manifest',str(root/'MANIFEST.json'),'--report',str(root/'REPORT.md'),'--final-sha256',a['FINAL'],'--manifest-sha256',a['MANIFEST'],'--report-sha256',a['REPORT']]
def run(argv):return subprocess.run(argv,capture_output=True,text=True)
before=observe(R);ab=observe(A);assert ab==read(P.parent/'observed-root.json')
v=run(command(R,anchors));assert v.returncode==0,(v.stdout,v.stderr)
files=[e for e in read(R/'MANIFEST.json')['entries'] if e['type']=='file'];assert len(files)==43 and sum(e['size'] for e in files)==4150368
assert sha((R/'packet/REVIEW.md').read_bytes())=='e686486c923156a7a2484c99ea5f882b7518946f36b503caadf9496b5722e39d'
assert sha((R/'verify_packet.py').read_bytes())=='8b8b7e7e987cb0ac5cee94ed9e7a0aa33a5d4c21b72bf59a284bfb744bffe038'
assert sha((R/'controls/results.json').read_bytes())=='e5c162a3d7561009314acf1709017a140ab67eb4d05b5eebe464717e8a054e40'
assert sha((R/'controls/MANIFEST.json').read_bytes())=='69ec837732b818d1add37e09934dcc1ac0360c52ce9ed562caa6e9db7424c913'
assert sha((R/'controls/REPORT.md').read_bytes())=='d42ad35603a5d4e31d6b90edfa82d39cb690241c66ab496fc23130f4050b8513'
rb=read(D/'author-before.json');assert rb==read(D/'author-after.json') and len(rb)==50
for e in rb:
    x=ab[(PROJECT/e['path']).relative_to(A).as_posix()]
    assert e['regular'] and x['type']=='file' and (x['mode'],x['bytes'],x['sha256'])==(e['mode'],e['size'],e['sha256'])
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree={e['path']:e for e in json.loads(tb)['tree']}
canon=read(D/'source-authentication.json')['canonical'];assert len(canon)==5
for e in canon:
    b=(A/'packet/private/upstream'/e['path']).read_bytes();t=tree[e['path']]
    assert len(b)==e['size']==t['size'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob_sha1']==t['sha']
for e in read(D/'direct-reads.json')['direct']:
    lo,hi=e['read']
    with (PROJECT/e['path']).open('rb') as f:f.seek(lo);b=f.read(hi-lo)
    assert len(b)==hi-lo and sha(b)==e['sha256']
for e in read(D/'history-reads.json'):
    lo,hi=e['bytes_half_open']
    with (PROJECT/e['path']).open('rb') as f:f.seek(lo);b=f.read(hi-lo)
    assert len(b)==hi-lo and sha(b)==e['selected_sha256']
primaries=read(D/'primary-reads.json');assert len(primaries)==7
for e in primaries:
    p=PROJECT/e['file'];b=p.read_bytes();assert sha(b)==e['text_sha256']
    if 'pdf_sha256' in e:assert sha(p.with_suffix('.pdf').read_bytes())==e['pdf_sha256']
    for lo,hi in e.get('reads_bytes_half_open',[]):assert 0<=lo<hi<=len(b)
    if 'text_bytes_presented' in e:assert e['text_bytes_presented']==[0,len(b)]
    for page in e.get('scan_recovered_text_page_extents',[]):
        lo,hi=page['extracted_text_bytes_half_open'];assert 0<=lo<hi<=len(b)
for name in ['access.json','brunel-access.json']:
    for e in read(D/'retrieval'/name):
        if 'sha256' not in e:continue
        ext='.pdf' if e.get('pdf',True) else '.response';b=(D/'retrieval'/(e['name']+ext)).read_bytes()
        assert len(b)==e['bytes'] and sha(b)==e['sha256']
controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as tmp:
    dst=Path(tmp)/'fixture';shutil.copytree(R/'controls',dst);p=dst/'packet/SCOPE.txt';original=p.read_bytes();original_mode=p.stat().st_mode & 0o777
    a={'FINAL':sha((dst/'packet/FINAL.md').read_bytes()),'MANIFEST':sha((dst/'MANIFEST.json').read_bytes()),'REPORT':sha((dst/'REPORT.md').read_bytes())}
    def check(name,a,wanted):
        q=run(command(dst,a));ok=q.returncode==0;assert ok==wanted,(name,q.stdout,q.stderr);controls.append({'case':name,'accepted':ok,'expected':wanted})
    check('intact',a,True)
    p.write_bytes(original+b'!');check('changed-bytes',a,False);p.write_bytes(original)
    extra=dst/'packet/extra';extra.mkdir();check('extra-directory',a,False);extra.rmdir()
    p.chmod(0o400);check('changed-mode',a,False);p.chmod(original_mode)
    check('wrong-anchor',dict(a,MANIFEST='0'*64),False);check('restored',a,True)
assert observe(R)==before and observe(A)==ab
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':json.loads(v.stdout),'selected_content_bytes':4150368,'root_files':sum(e['type']=='file' for e in before.values()),'root_directories':sum(e['type']=='directory' for e in before.values()),'author_files':50,'author_directories':14,'author_bytes_modes_unchanged':True,'review_bytes_modes_unchanged':True,'reviewer_author_file_baseline':50,'reviewer_outside_directory_baseline_claimed':False,'canonical_blobs':5,'primary_text_bindings':7,'primary_pdf_bindings':7,'new_retrieval_response_bindings':1,'render_files_integrity_only':12,'history_spans':3,'direct_input_bindings':4,'copied_controls':controls,'frozen_statement_sha256':sha((A/'packet/FROZEN.md').read_bytes()),'author_proof_sha256':sha((A/'packet/DERIVATION.md').read_bytes()),'review_sha256':sha((R/'packet/REVIEW.md').read_bytes()),'limits':'Full review/report/handoff and evidence metadata read; source/primary/history bodies and renders integrity-bound only by parent in this adoption. Selected packet paths/modes/content are manifest-bound; outside verifier/control hashes bind through anchored REPORT. Outside selection/modes are parent observations only. Reviewer before/after baseline covers 50 author files; parent baseline covers 50 files and14 directories.'}
for name,value in [('replay.json',out),('observed-root.json',before)]:
    p=P/name;p.write_text(json.dumps(value,indent=2)+'\n');p.chmod(0o600)
print(json.dumps(out,indent=2))
