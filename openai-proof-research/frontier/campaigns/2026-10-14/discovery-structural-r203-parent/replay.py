#!/usr/bin/env python3
"""Authenticate the exact author packet and receipts; never edit its originals."""
from pathlib import Path
import datetime,hashlib,json,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2];R=C/'fresh-structural-discovery-r203';A=R/'packet';D=A/'private'
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest();mode=lambda p:format(stat.S_IMODE(p.stat().st_mode),'04o')
anchors={'FINAL':'3390497b1ed8e1b32c2d77b1cf9b8fa56d6880285414f9043beed85b26e863c9','MANIFEST':'4b5e26efaa6fde529234c696e6d227e35e04a51ca160885860ba17f3cb7d57e7','REPORT':'f2bc08bd10a6b98ecb7fe02d31f45d921bcedf191d6dc456c12cf38793f32971'}
def observe():
    out={'.':{'type':'directory','mode':mode(R)}}
    for p in sorted(R.rglob('*')):
        assert not p.is_symlink();e={'type':'directory' if p.is_dir() else 'file','mode':mode(p)}
        if p.is_file():b=p.read_bytes();e.update(bytes=len(b),sha256=sha(b))
        out[p.relative_to(R).as_posix()]=e
    return out
def verify(packet,manifest,report,a):
    return subprocess.run(['python3','-I','-B',str(R/'verify_packet.py'),'--packet',str(packet),'--manifest',str(manifest),'--report',str(report),'--final-sha256',a['FINAL'],'--manifest-sha256',a['MANIFEST'],'--report-sha256',a['REPORT']],capture_output=True,text=True)
before=observe();baseline=P/'observed-root.json'
if baseline.exists():assert read(baseline)==before
else:baseline.write_text(json.dumps(before,indent=2)+'\n');baseline.chmod(0o600)
v=verify(A,R/'MANIFEST.json',R/'REPORT.md',anchors);assert v.returncode==0,(v.stdout,v.stderr)
m=read(R/'MANIFEST.json');selected=[e for e in m['entries'] if e['type']=='file'];assert len(selected)==40 and sum(e['size'] for e in selected)==5134355
freeze=read(D/'freeze-anchor.json');assert sha((A/'FROZEN.md').read_bytes())==freeze['sha256']=='850bd50cd2888d4f184e8b164f1e8dfbd2258181f65adf22dc4b21d71ea52576'
assert sha((A/'DERIVATION.md').read_bytes())=='64383e9146d43df52931ad2982b49bd1887660298803081835dde44d79d18f67'
assert sha((R/'verify_packet.py').read_bytes())=='0430c5b4d65fd1e15b8b6ed5ea50fcdd584558ef47e98fc6518d2f69d85b6369'
assert sha((R/'controls/results.json').read_bytes())=='2589193960cbc59dc3ca9c503a9ffa1d41f604fc46d127ff23a5920c9addd0c3'
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree={e['path']:e for e in json.loads(tb)['tree']}
auth=read(D/'source-authentication.json');canonical=0;formal=set()
for e in auth:
    path=e['path'];b=(D/'upstream'/path).read_bytes();assert len(b)==e['size'] and sha(b)==e['sha256']
    if 'git_blob_sha1' in e:assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob_sha1']
    if path.startswith('preprints/'):
        t=tree[path];assert t['size']==len(b) and t['sha']==e['git_blob_sha1'];canonical+=1
    else:formal.add(path)
assert canonical==5 and len(formal)==2
assert (D/'lean-doc-327.md').read_bytes()==(D/'upstream/lean/docs/327.md').read_bytes()
log=read(D/'reading-log.json');main=D/'upstream/preprints/Nontrivial-Markov-Type-Forces-Superreflexivity-September-23-2026/build/main.tex'
parts=[e for e in log['source_semantic_reads'] if e['path']=='canonical build/main.tex'];assert [e['bytes_half_open'] for e in parts]==[[0,10547],[10547,22651],[22651,32770],[32770,42458]] and main.stat().st_size==42458
for e in log['source_semantic_reads']:
    if e['path']!='canonical build/main.tex':assert e['bytes_half_open']==[0,(D/'upstream'/e['path']).stat().st_size]
primary=read(D/'primary-access.json');success=[e for e in primary if 'sha256' in e];assert len(success)==4
for e in success:
    b=(D/'primary'/(e['name']+'.pdf')).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256']
for e in read(D/'primary-read-extents.json'):
    b=(D/'primary'/(e['name']+'.txt')).read_bytes();assert sha(b)==e['text_sha256'];lo,hi=e['bytes'];assert 0<=lo<hi<=len(b)
history=read(D/'history-read-extents.json');assert len(history)==3
copies=['original-i88-section.md','original-i104-section.md','original-i88-Markov-section.md']
for e,name in zip(history,copies):
    lo,hi=e['bytes']
    with (PROJECT/e['path']).open('rb') as stream:stream.seek(lo);b=stream.read(hi-lo)
    assert sha(b)==e['sha256_selected'] and b==(D/name).read_bytes()
for path,lo,hi,h in [('sources/CONTENTS.md',553766,554644,'c0d699fee3021aab9535dd222c6ad9689535d1a0262c0944d807c2c5d7e00828'),('frontier/NEW-TEN-2026-10-14.md',4801,6347,'f147924a01d36cce7ad5ee13bad6ed9ed9109f3bf4b5c2386fc318aae1330984')]:
    with (PROJECT/path).open('rb') as stream:stream.seek(lo);b=stream.read(hi-lo)
    assert sha(b)==h
    if path.startswith('sources/'):assert b==(D/'Source327-catalogue.txt').read_bytes()
controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as tmp:
    for case in ['exact','changed-bytes','extra-directory','changed-mode','wrong-anchor']:
        dst=Path(tmp)/case;shutil.copytree(R/'controls',dst);p=dst/'packet';mf=dst/'MANIFEST.json';rf=dst/'REPORT.md'
        a={'FINAL':sha((p/'FINAL.md').read_bytes()),'MANIFEST':sha(mf.read_bytes()),'REPORT':sha(rf.read_bytes())}
        if case=='changed-bytes':(p/'FROZEN.md').write_bytes((p/'FROZEN.md').read_bytes()+b'!')
        elif case=='extra-directory':(p/'extra').mkdir()
        elif case=='changed-mode':(p/'FROZEN.md').chmod(0o600)
        elif case=='wrong-anchor':a['MANIFEST']='0'*64
        q=verify(p,mf,rf,a);ok=q.returncode==0;assert ok==(case=='exact'),(case,q.stdout,q.stderr);controls.append({'case':case,'accepted':ok,'expected':case=='exact'})
assert observe()==before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':json.loads(v.stdout),'selected_files':40,'selected_directories':11,'selected_bytes':5134355,'canonical_blobs':5,'formal_file_bindings':2,'source_semantic_extent_bindings':9,'primary_pdf_bindings':4,'primary_text_extent_bindings':6,'history_exact_spans':3,'catalogue_acceptance_spans':2,'copied_controls':controls,'root_files':sum(e['type']=='file' for e in before.values()),'root_directories':sum(e['type']=='directory' for e in before.values()),'author_bytes_modes_unchanged':True,'frozen_statement_sha256':freeze['sha256'],'author_proof_sha256':sha((A/'DERIVATION.md').read_bytes()),'frozen_utc':freeze['frozen_at_utc'],'limits':'Manifest binds the entire packet directory, file/directory types, modes and bytes. Outside MANIFEST/REPORT and selected FINAL have explicit detached anchors. Other root controls, verifier, ANCHORS, VERIFICATION and outside modes are not members of that selected packet; parent separately baselines every observed file/directory and checks stated verifier/control-result hashes. Receipt/hash binding is not semantic reading.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');(P/'replay.json').chmod(0o600);print(json.dumps(out,indent=2))
