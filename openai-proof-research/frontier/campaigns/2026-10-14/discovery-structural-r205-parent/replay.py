#!/usr/bin/env python3
"""Read-only r205 archive replay, with tiny controls copied into the parent root."""
from pathlib import Path
import datetime,hashlib,json,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2];R=C/'fresh-structural-discovery-r205';D=R/'private'
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'6e0af78dd79a7b50ae37adf59e209e1c824ce68462d408c0e8992f8a66cae64f','MANIFEST':'f3f916b1aca22c523efb267ab85fa3286efa54acebee5f6528a42bdd855f265f','REPORT':'972a79954ea8d61e47047635974a7f97684372adca7c2ac5b070d69f4455efe2'}
def observe(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        assert not p.is_symlink();e={'type':'directory' if p.is_dir() else 'file','mode':format(stat.S_IMODE(p.stat().st_mode),'04o')}
        if p.is_file():b=p.read_bytes();e.update(bytes=len(b),sha256=sha(b))
        out['.' if p==root else p.relative_to(root).as_posix()]=e
    return out
def command(root,a):return ['python3','-I','-B',str(R/'verify_packet.py'),'--root',str(root),'--final-sha256',a['FINAL'],'--manifest-sha256',a['MANIFEST'],'--report-sha256',a['REPORT']]
def run(args):return subprocess.run(args,capture_output=True,text=True)
before=observe(R)
for k in anchors:assert sha((R/({'FINAL':'FINAL.md','MANIFEST':'MANIFEST.json','REPORT':'REPORT.md'}[k])).read_bytes())==anchors[k]
v=run(command(R,anchors));assert v.returncode==0,(v.stdout,v.stderr)
m=read(R/'MANIFEST.json');assert len(m['files'])==72 and sum(e['bytes'] for e in m['files'])==2850725 and len(m['directories'])==7
assert m['outside_files']==['MANIFEST.json','REPORT.md','ANCHORS.json','verification.json'] and m['outside_directories']==['controls']
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree={e['path']:e for e in json.loads(tb)['tree']}
auth=read(D/'authentication.json');canon=[e for e in auth if e['path'].startswith('preprints/')];assert len(canon)==11
for e in canon:
    b=(R/e['local']).read_bytes();t=tree[e['path']]
    assert len(b)==e['size']==t['size'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['sha']==t['sha']
for name,meta in [('lean-329.md','lean-329-metadata.json'),('MetricEntropyDuality.lean','comparator-auth.json')]:
    e=read(D/meta);b=(D/name).read_bytes();assert len(b)==e['size'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['sha']
    if 'sha256' in e:assert sha(b)==e['sha256']
for e in read(D/'direct-read-record.json'):
    if not isinstance(e['bytes'],list):continue
    lo,hi=e['bytes']
    with (PROJECT/e['path']).open('rb') as f:f.seek(lo);b=f.read(hi-lo)
    assert len(b)==hi-lo and sha(b)==e['sha256']
history=0
for record in ['original-extents.json','primitive-extents.json']:
    for e in read(D/record):
        if 'false_admission' in e:continue
        lo,hi=e['start_byte'],e['end_byte_exclusive']
        with (PROJECT/e['path']).open('rb') as f:f.seek(lo);b=f.read(hi-lo)
        assert len(b)==hi-lo and sha(b)==e['section_sha256'] and b==(R/e['local']).read_bytes();history+=1
assert history==10
for e in read(D/'primary/retrieval.json'):
    b=(D/'primary'/(e['name']+'.pdf')).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256']
for e in read(D/'primary/rbg-retrieval.json'):
    if 'sha256' in e:
        b=(D/'primary/rbg2001.pdf').read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256']
extent_count=0
for name in ['read-extents-a.json','read-extents-b.json','read-extents-c.json','read-extents-rbg.json','complete-section-boundaries.json']:
    for e in read(D/'primary'/name):
        b=(D/'primary'/(e['name']+'.txt')).read_bytes();assert 0<=e['byte_start']<e['byte_end']<=len(b)
        expected=e.get('sha256_text',e.get('text_sha256'))
        if expected:assert sha(b)==expected
        extent_count+=1
controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as tmp:
    base=R/'controls/baseline';a={k:sha((base/f).read_bytes()) for k,f in [('FINAL','FINAL.md'),('MANIFEST','MANIFEST.json'),('REPORT','REPORT.md')]}
    for case in ['intact','changed-content','changed-mode','extra-selection']:
        dst=Path(tmp)/case;shutil.copytree(base,dst);f=dst/'derivations.md'
        if case=='changed-content':b=f.read_bytes();f.chmod(0o644);f.write_bytes(b+b'!');f.chmod(0o444)
        elif case=='changed-mode':f.chmod(0o644)
        elif case=='extra-selection':(dst/'extra.txt').write_text('extra\n')
        q=run(command(dst,a));accepted=q.returncode==0;assert accepted==(case=='intact'),(case,q.stdout,q.stderr);controls.append({'case':case,'accepted':accepted,'expected':case=='intact'})
assert observe(R)==before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':json.loads(v.stdout),'selected_directories':7,'root_files':sum(e['type']=='file' for e in before.values()),'root_directories':sum(e['type']=='directory' for e in before.values()),'originals_bytes_modes_unchanged':True,'canonical_blobs':11,'formal_bindings':2,'primary_pdf_bindings':6,'primary_extent_records':extent_count,'history_exact_spans':history,'direct_input_spans':4,'renders_integrity_only':1,'copied_controls':controls,'reduction_sha256':sha((R/'reduction.md').read_bytes()),'derivations_sha256':sha((R/'derivations.md').read_bytes()),'verifier_sha256':sha((R/'verify_packet.py').read_bytes()),'limits':'Full original research notes, final/report and reading/access metadata read by parent; underlying source/primary/history bodies and render integrity-bound only. Manifest selects72 files and7 directory modes, excluding its declared outside files and controls directory. Outside contents/modes are parent-baselined; detached anchors bind FINAL/MANIFEST/REPORT content. Metadata false admission was not opened. No mathematical gate.'}
for name,value in [('replay.json',out),('observed-root.json',before)]:
    p=P/name;p.write_text(json.dumps(value,indent=2)+'\n');p.chmod(0o600)
print(json.dumps(out,indent=2))
