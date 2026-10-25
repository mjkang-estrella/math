#!/usr/bin/env python3
"""Read-only independent S238 correctness-review artifact replay."""
from pathlib import Path
import datetime, hashlib, json, os, stat, subprocess, sys, tempfile

P=Path(__file__).resolve().parent; C=P.parents[1]; PROJECT=C.parents[2]
R=P.parent/'structural-r238-proof-r1'; K=R/'packet'
A=P.parent/'fresh-structural-discovery-r238'; AK=A/'packet'
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'packet/FINAL.md':'5fd6b7cb96a83293eb728abb78dbd323e8e26fbe7ee2761f6dd32a67074d964e','packet/MANIFEST.json':'7f410bc730058cab5ce1f0d6c6b0ffae19ad1d97fe0a3e1bf1a2ab7b8816c889','REPORT.md':'d87665889f1c5dfcf4da094d34a2372db62af5a171410beabacae2f590074144'}
def inventory(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        assert not p.is_symlink();n=p.relative_to(root).as_posix();mode=oct(stat.S_IMODE(p.stat().st_mode))
        if p.is_dir():out[n]={'type':'dir','mode':mode}
        else:
            assert p.is_file();b=p.read_bytes();out[n]={'type':'file','mode':mode,'bytes':len(b),'sha256':sha(b)}
    return out
before=inventory(R);author_before=inventory(A)
assert author_before==read(P.parent/'discovery-structural-r238-parent/observed-root.json')
for n,h in anchors.items():assert sha((R/n).read_bytes())==h
v=K/'verify_packet.py'
assert sha(v.read_bytes())=='66a416a61bbd047f494d43feed7ff51afd1d990bdabfc14cd7bf1688b970b91a'
def call(root,mh,fh,report,rh):
    return subprocess.run([sys.executable,'-I','-B',str(v),'--packet',str(root),'--manifest-sha256',mh,'--final-sha256',fh,'--report',str(report),'--report-sha256',rh],capture_output=True,text=True)
result=call(K,anchors['packet/MANIFEST.json'],anchors['packet/FINAL.md'],R/'REPORT.md',anchors['REPORT.md'])
assert result.returncode==0,result.stderr;verified=json.loads(result.stdout)
assert (verified['files'],verified['directories'])==(13,2)
am=read(AK/'MANIFEST.json');admitted={str((AK/x['path']).relative_to(PROJECT))for x in am['files']}
admitted.add(str((AK/'MANIFEST.json').relative_to(PROJECT)))
admitted.update(str((A/n).relative_to(PROJECT))for n in ['REPORT.md','PACKET-ANCHORS.json','VERIFICATION.json'])
baseline=read(K/'private/original-baseline.json')
assert len(baseline['files'])==83 and {x['path']for x in baseline['files']}==admitted
for x in baseline['files']:
    p=PROJECT/x['path'];b=p.read_bytes();assert len(b)==x['bytes']and sha(b)==x['sha256']and f'{stat.S_IMODE(p.stat().st_mode):04o}'==x['mode']
dirs={str((AK/x['path']).relative_to(PROJECT)):x['mode']for x in am['directories']}
assert len(baseline['directories'])==14 and {x['path']:x['mode']for x in baseline['directories']}==dirs
for path,mode in dirs.items():assert f'{stat.S_IMODE((PROJECT/path).stat().st_mode):04o}'==mode
assert read(K/'private/originals-after-reading.json')['all_bytes_hashes_modes_unchanged']
assert read(K/'private/inherited-guards.json')==read(AK/'private/guards.json')
assert (len(read(K/'private/inherited-guards.json')['wildcards']),len(read(K/'private/inherited-guards.json')['substrings']))==(399,162)

tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert len(tb)==4858136 and sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(tb);entries=tree['tree']if isinstance(tree,dict)else tree;assert len(entries)==13223
sel=read(AK/'private/tree-selection.json');assert sel==[x for x in entries if 'boltzmann'in x['path'].casefold()and 'nonuniqueness'in x['path'].casefold()]
lookup={x['path']:x for x in sel};auth=read(AK/'private/canonical-auth.json');assert len(auth)==35
for x in auth:
    b=(AK/'private/canonical'/x['path']).read_bytes();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    assert len(b)==x['bytes']and sha(b)==x['sha256']and blob==x['git_blob']==lookup[x['path']]['sha']
sc=read(K/'private/source-auth-check.json');assert sc=={'pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','entries':43,'blobs':35,'full_tree_sha256':sha(tb)}
rr=[json.loads(x)for x in(K/'private/review-reads.jsonl').read_bytes().splitlines()]
for x in rr:
    assert x['path']in admitted;b=(PROJECT/x['path']).read_bytes();lines=b.splitlines(keepends=True);lo,hi=x['lines']
    assert 1<=lo<=hi<=len(lines)and sha(b)==x['sha256']
    assert x['byte_range']==[sum(map(len,lines[:lo-1])),sum(map(len,lines[:hi]))]
    assert all(lo<=n<=hi for n in x['masked_lines'])
coverage=read(K/'private/reviewer-source-coverage.json')['files'];assert len(coverage)==31
for x in coverage:
    assert x['path']in admitted;lines=(PROJECT/x['path']).read_bytes().splitlines(keepends=True);assert len(lines)==x['lines']
    chosen=set()
    for lo,hi in x['ranges']:chosen.update(range(lo,hi+1))
    assert sorted(set(range(1,len(lines)+1))-chosen)==x['unselected_lines']==[]
    recorded=set()
    for y in rr:
        if y['path']==x['path']:recorded.update(range(y['lines'][0],y['lines'][1]+1))
    assert chosen<=recorded
pr=[json.loads(x)for x in(K/'private/primary-review-reads.jsonl').read_bytes().splitlines()]
for x in pr:
    p=AK/x['file'];assert str(p.relative_to(PROJECT))in admitted;b=p.read_bytes();lines=b.splitlines(keepends=True);lo,hi=x['start'],x['end']
    assert sha(b)==x['sha256']and 1<=lo<=hi<=len(lines)
    assert (x['start_byte'],x['end_byte'])==(sum(map(len,lines[:lo-1])),sum(map(len,lines[:hi])))
    assert all(lo<=n<=hi for n in x['masked'])

controls=[]
with tempfile.TemporaryDirectory(prefix='proof-tiny-controls-',dir=P)as td:
    root=Path(td)/'packet';root.mkdir();f=root/'FINAL.md';f.write_bytes(b'tiny final\n');os.chmod(f,0o444)
    report=Path(td)/'REPORT.md';report.write_bytes(b'tiny report\n');os.chmod(report,0o444)
    m={'schema':'s238-independent-correctness-selection-v1','files':[{'path':'FINAL.md','bytes':len(f.read_bytes()),'sha256':sha(f.read_bytes()),'mode':'0444'}],'directories':[{'path':'.','mode':f'{stat.S_IMODE(root.stat().st_mode):04o}'}]}
    mf=root/'MANIFEST.json';mf.write_text(json.dumps(m));os.chmod(mf,0o444)
    args=(root,sha(mf.read_bytes()),sha(f.read_bytes()),report,sha(report.read_bytes()))
    def control(label,reject=False,arguments=args):
        z=call(*arguments);assert (z.returncode!=0)==reject
        controls.append({'case':label,'rejected':reject,'exit_code':z.returncode})
    control('intact');saved=f.read_bytes();os.chmod(f,0o644);f.write_bytes(saved+b'x');os.chmod(f,0o444);control('changed bytes',True)
    os.chmod(f,0o644);f.write_bytes(saved);control('changed mode',True);os.chmod(f,0o444)
    (root/'extra').write_bytes(b'x');control('extra file',True);(root/'extra').unlink()
    (root/'extra-dir').mkdir();control('extra directory',True);(root/'extra-dir').rmdir()
    f.rename(root/'missing');control('omitted file',True);(root/'missing').rename(f)
    control('wrong detached report hash',True,args[:-1]+('0'*64,));control('restored')
assert inventory(R)==before and inventory(A)==author_before
(P/'proof-observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'packet_verification':verified,'selected_files_excluding_manifest':13,'packet_files_including_manifest':14,'packet_directories_including_root':2,'review_whole_files':sum(x['type']=='file'for x in before.values()),'review_whole_directories_including_root':sum(x['type']=='dir'for x in before.values()),'review_originals_unchanged':True,'admitted_author_files':83,'admitted_author_directory_modes':14,'author_whole_files':sum(x['type']=='file'for x in author_before.values()),'author_originals_unchanged':True,'canonical_blobs_authenticated':35,'canonical_tree_entries':43,'recorded_general_read_intervals_bound':len(rr),'complete_source_file_selections_bound':31,'primary_read_intervals_bound':len(pr),'independent_primary_documents_recorded':len({x['file']for x in pr}),'guards':{'wildcards':399,'substrings':162},'tiny_copied_controls':controls,'mathematical_scope':'Artifact and provenance replay only; reading logs do not transfer semantic or visual coverage to the parent.'}
(P/'proof-replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
