#!/usr/bin/env python3
"""Read-only independent S238 contribution-review artifact replay."""
from pathlib import Path
import datetime, fnmatch, hashlib, json, os, stat, subprocess, sys, tempfile

P=Path(__file__).resolve().parent; C=P.parents[1]; PROJECT=C.parents[2]
R=P.parent/'structural-r238-contribution-r1'; K=R/'packet'
A=P.parent/'fresh-structural-discovery-r238'; AK=A/'packet'
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'packet/FINAL.md':'3b62e8497c30216f6326e55de74ca8fc0d3cb761b53d57cb15a720ce06a19144','packet/MANIFEST.json':'d1536f0ba8db8d79d44c9821c61003917ac5168f20540714573a452b3b245099','REPORT.md':'5156690c1c32d021c509c61286945060c46e93a204d5e1ddee34f4f03d9a3f04'}
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
assert sha(v.read_bytes())=='0f14d28f11b0decedf6e7873491dc396b63f7c7f5082c3a3843324b918abcbdd'
def call(root,mh,fh,report,rh):
    return subprocess.run([sys.executable,'-I','-B',str(v),'--packet',str(root),'--manifest-sha256',mh,'--final-sha256',fh,'--report',str(report),'--report-sha256',rh],capture_output=True,text=True)
result=call(K,anchors['packet/MANIFEST.json'],anchors['packet/FINAL.md'],R/'REPORT.md',anchors['REPORT.md'])
assert result.returncode==0,result.stderr;verified=json.loads(result.stdout)
assert (verified['selected_files'],verified['directories'])==(19,2)
am=read(AK/'MANIFEST.json');admitted={str((AK/x['path']).relative_to(PROJECT))for x in am['files']}
admitted.add(str((AK/'MANIFEST.json').relative_to(PROJECT)))
admitted.update(str((A/n).relative_to(PROJECT))for n in ['REPORT.md','PACKET-ANCHORS.json','VERIFICATION.json'])
baseline=read(K/'private/original-baseline.json')
assert len(baseline['files'])==83 and {x['path']for x in baseline['files']}==admitted
for x in baseline['files']:
    p=PROJECT/x['path'];b=p.read_bytes();assert len(b)==x['bytes']and sha(b)==x['sha256']and stat.S_IMODE(p.stat().st_mode)==int(x['mode'],8)
dirs={str((AK/x['path']).relative_to(PROJECT)):x['mode']for x in am['directories']}
assert len(baseline['directories'])==14 and {x['path']:int(x['mode'],8)for x in baseline['directories']}=={k:int(v,8)for k,v in dirs.items()}
for path,mode in dirs.items():assert f'{stat.S_IMODE((PROJECT/path).stat().st_mode):04o}'==mode
assert read(K/'private/original-recheck-before-seal.json')['unchanged']
guards=read(K/'private/guards.json');original_guards=read(AK/'private/guards.json')
assert set(guards['wildcards'])==set(original_guards['wildcards']) and set(guards['substrings'])==set(original_guards['substrings'])
assert (len(guards['wildcards']),len(guards['substrings']))==(399,162)
prior_review=P.parent/'structural-r238-proof-r1'
prior_review_before=inventory(prior_review);assert prior_review_before==read(P/'proof-observed-root.json')

tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert len(tb)==4858136 and sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(tb);entries=tree['tree']if isinstance(tree,dict)else tree;assert len(entries)==13223
sel=read(AK/'private/tree-selection.json');assert sel==[x for x in entries if 'boltzmann'in x['path'].casefold()and 'nonuniqueness'in x['path'].casefold()]
lookup={x['path']:x for x in sel};auth=read(AK/'private/canonical-auth.json');assert len(auth)==35
for x in auth:
    b=(AK/'private/canonical'/x['path']).read_bytes();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    assert len(b)==x['bytes']and sha(b)==x['sha256']and blob==x['git_blob']==lookup[x['path']]['sha']
sc=read(K/'private/source-authentication.json')
assert sc['tree_sha256']==sha(tb) and sc['entries']==13223 and sc['selection_entries']==43 and sc['blobs']==35 and sc['all_git_blob_hashes_match']
rr=[json.loads(x)for x in(K/'private/source-reads.jsonl').read_bytes().splitlines()]
coverage={}
for x in rr:
    p=AK/x['file'];assert str(p.relative_to(PROJECT))in admitted;b=p.read_bytes();lines=b.splitlines(keepends=True);lo,hi=x['lines']
    assert 1<=lo<=hi<=len(lines)and sha(b)==x['sha256']
    assert x['bytes']==[sum(map(len,lines[:lo-1])),sum(map(len,lines[:hi]))]
    assert all(lo<=n<=hi for n in x['masked'])
    coverage.setdefault(x['file'],set()).update(range(lo,hi+1))
assert len(coverage)==31
for name,selected in coverage.items():assert selected==set(range(1,len((AK/name).read_bytes().splitlines(keepends=True))+1))
pr=[json.loads(x)for x in(K/'private/primary-reads.jsonl').read_bytes().splitlines()]
for x in pr:
    p=AK/'private/primary'/(x['id']+'.txt');assert str(p.relative_to(PROJECT))in admitted;b=p.read_bytes();lines=b.splitlines(keepends=True);lo,hi=x['line_start'],x['line_end_inclusive']
    assert sha(b)==x['source_sha256']and 1<=lo<=hi<=len(lines)
    assert (x['byte_start'],x['byte_end_exclusive'])==(sum(map(len,lines[:lo-1])),sum(map(len,lines[:hi])))
    assert all(lo<=n<=hi for n in x['masked_running_headers'])
versions=read(K/'private/primary-versions.json');assert len(versions)==7
for x in versions:
    for ext in ['pdf','txt']:
        p=AK/'private/primary'/(x['id']+'.'+ext);assert str(p.relative_to(PROJECT))in admitted;b=p.read_bytes();assert len(b)==x[ext]['bytes']and sha(b)==x[ext]['sha256']
h=read(K/'private/history-reads.json');path=h['path'];fold=path.casefold()
assert not any(fnmatch.fnmatchcase(fold,pat.casefold())for pat in guards['wildcards'])
assert not any(term.casefold()in fold for term in guards['substrings'])
assert not any(fnmatch.fnmatchcase(component,pat)for component in Path(fold).parts for pat in guards['additional_component_patterns'])
hp=PROJECT/path;assert not hp.is_symlink();hb=hp.read_bytes();assert sha(hb)==h['sha256'];hl=hb.splitlines(keepends=True)
assert h['ranges']==[[5,63],[68,120]]
for lo,hi in h['ranges']:
    assert hl[lo-1].startswith(b'## ') and hl[hi].startswith(b'## ')
history_identity={'files':1,'ranges':2,'guarded_before_read':True,'parent_semantic_body_read':False}

controls=[]
with tempfile.TemporaryDirectory(prefix='contribution-tiny-controls-',dir=P)as td:
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
assert inventory(R)==before and inventory(A)==author_before and inventory(prior_review)==prior_review_before
(P/'contribution-observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'packet_verification':verified,'selected_files_excluding_manifest':19,'packet_files_including_manifest':20,'packet_directories_including_root':2,'review_whole_files':sum(x['type']=='file'for x in before.values()),'review_whole_directories_including_root':sum(x['type']=='dir'for x in before.values()),'review_originals_unchanged':True,'admitted_author_files':83,'admitted_author_directory_modes':14,'author_whole_files':sum(x['type']=='file'for x in author_before.values()),'author_originals_unchanged':True,'canonical_blobs_authenticated':35,'canonical_tree_entries':43,'recorded_source_read_intervals_bound':len(rr),'complete_source_file_selections_bound':31,'primary_read_intervals_bound':len(pr),'independent_primary_documents_recorded':len({x['id']for x in pr}),'guards':{'wildcards':399,'substrings':162},'tiny_copied_controls':controls,'primary_pdf_text_identities_bound':len(versions),'history_identity':history_identity,'prior_correctness_review_unchanged':True,'mathematical_scope':'Artifact and provenance replay only; reading logs do not transfer semantic or visual coverage to the parent.'}
(P/'contribution-replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
