#!/usr/bin/env python3
"""Read-only contribution artifact intake. Identity binding is not proof reading."""
from pathlib import Path
import datetime,hashlib,json,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2]
R=C/'structural-r216-contribution-r1';K=R/'packet';A=C/'fresh-structural-discovery-r216'
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'3d2306878dfbf807cbf4503d3033e0b0254a564e3f460c31dd1d85163e6a2fae','MANIFEST':'b1aacab665e6214493fbe0fb6246b60b38f0ccdd2d51f5c42ef6fd7930a545ed','SELECTION':'edc92b70a6f53083f558059413ac3dfd8b62b669929f6d9351040506cd0e33a6','REPORT':'e4421d018665eabff32cc0b553178559afbf49b7adcb9579ed1dab6f732acf7c'}
def observe(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        assert not p.is_symlink()
        e={'type':'directory' if p.is_dir() else 'file','mode':format(stat.S_IMODE(p.stat().st_mode),'04o')}
        if p.is_file():b=p.read_bytes();e.update(bytes=len(b),sha256=sha(b))
        out['.' if p==root else p.relative_to(root).as_posix()]=e
    return out
def run(root,a):
    args=['python3','-I','-B',str(R/'verify_packet.py'),'--packet',str(root/'packet')]
    for n in ['manifest','selection','report']:args.extend(['--'+n,str(root/(n.upper()+('.md' if n=='report' else '.json')))])
    for n in anchors:args.extend(['--'+n.lower()+'-sha',a[n]])
    return subprocess.run(args,capture_output=True,text=True)
before=observe(R);author_before=observe(A)
assert author_before==read(C/'discovery-structural-r216-parent/observed-root.json')
assert sha((R/'verify_packet.py').read_bytes())=='7b6ebc45e4f6d7ade695a45363eef5b1b25d5482ab9a94c1ac7561342554df38'
v=run(R,anchors);assert v.returncode==0,(v.stdout,v.stderr)
ab=read(K/'private/admitted-originals-before.json');aa=read(K/'private/admitted-originals-after.json')
assert aa['admitted_files']==len(ab)==62 and aa['bytes_modes_unchanged'] and not aa['changes']
for e in ab:
    p=PROJECT/e['path'];assert p.is_relative_to(A);b=p.read_bytes()
    assert len(b)==e['size'] and sha(b)==e['sha256'] and oct(stat.S_IMODE(p.stat().st_mode))==e['mode']
for n in ['STATEMENT.md','AUTHOR-PROOF.md']:assert (K/'private/copies'/n).read_bytes()==(A/'packet'/n).read_bytes()
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree={e['path']:e for e in json.loads(tb)['tree']};source=read(K/'private/source-authentication.json')['entries']
prefix='preprints/A-counterexample-to-the-nearby-Lagrangian-conjecture-September-23-2026/'
assert len(source)==13 and {e['canonical'] for e in source}=={p for p,e in tree.items() if e['type']=='blob' and p.startswith(prefix)}
logs=[json.loads(s) for s in (K/'private/semantic-reads.jsonl').read_text().splitlines()];textcount=primary=0
for e in source:
    p=PROJECT/e['local'];assert p.is_relative_to(A);b=p.read_bytes();t=tree[e['canonical']]
    assert len(b)==e['bytes']==t['size'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_sha1']==t['sha']
    if p.suffix=='.pdf':continue
    intervals=sorted((x['byte_start'],x['byte_end']) for x in logs if x.get('path')==e['local']);end=0
    for lo,hi in intervals:assert 0<=lo<=end and lo<=hi<=len(b);end=max(end,hi)
    assert end==len(b);textcount+=1
for e in logs:
    p=PROJECT/e['path'];assert p.is_relative_to(A);b=p.read_bytes();lo,hi=e['byte_start'],e['byte_end']
    assert 0<=lo<=hi<=len(b)==e['file_bytes'] and sha(b)==e['file_sha256'] and sha(b[lo:hi])==e['selection_sha256']
    if '/private/primary/' in e['path']:primary+=1
w=read(K/'private/primary/Waldhausen1982-access.json');b=(K/'private/primary/Waldhausen1982.pdf').read_bytes();txt=(K/'private/primary/Waldhausen1982.txt').read_bytes()
assert len(b)==w['bytes'] and sha(b)==w['sha256'] and len(txt)==w['text_bytes']==44 and sha(txt)==w['text_sha256'] and txt==b'\f'*44
visual=read(K/'private/visual-reading.json');assert visual['pages_one_based']==[16,17,18,19]
for page in visual['pages_one_based']:assert (K/f'private/renders/AACK-{page}.png').is_file()
assert read(K/'private/history-scan.json')['semantic_body_reads']==0
controls=[]
with tempfile.TemporaryDirectory(prefix='contribution-controls-',dir=P) as tmp:
    base=R/'controls';ca={key:sha((base/('packet/FINAL.md' if key=='FINAL' else key+('.md' if key=='REPORT' else '.json'))).read_bytes()) for key in anchors}
    for case in ['intact','wrong-anchor','changed-bytes','extra-file','missing-file','file-mode','directory-mode']:
        dst=Path(tmp)/case;shutil.copytree(base,dst);a=dict(ca);f=dst/'packet/private/tiny-copy.txt'
        if case=='wrong-anchor':a['FINAL']='0'*64
        elif case=='changed-bytes':b=f.read_bytes();f.write_bytes(bytes([b[0]^1])+b[1:])
        elif case=='extra-file':(dst/'packet/extra.txt').write_text('extra\n')
        elif case=='missing-file':f.unlink()
        elif case=='file-mode':f.chmod(0o644)
        elif case=='directory-mode':(dst/'packet/private').chmod(0o755)
        q=run(dst,a);ok=q.returncode==0;assert ok==(case=='intact'),(case,q.stdout,q.stderr)
        controls.append({'case':case,'accepted':ok,'expected':case=='intact'})
assert observe(R)==before and observe(A)==author_before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':json.loads(v.stdout),'selected_subdirectories':sum(e['type']=='directory' and e['path']!='.' for e in read(R/'MANIFEST.json')['entries']),'review_root_files':sum(e['type']=='file' for e in before.values()),'review_root_directories':sum(e['type']=='directory' for e in before.values()),'review_originals_bytes_modes_unchanged':True,'admitted_author_files_unchanged':62,'whole_author_root_unchanged_since_parent_intake':True,'canonical_blobs':13,'complete_text_read_record_bindings':textcount,'semantic_extent_identity_bindings':len(logs),'primary_extent_identity_bindings':primary,'own_visual_page_identity_bindings':4,'additional_primary_pdf_identity_bindings':1,'additional_primary_semantic_coverage':False,'original_history_bodies_read':0,'copied_controls':controls,'formal_navigation':read(K/'private/formal-endpoint-access.json'),'verifier_anchor_discrepancy':'Same parent transcription error already recorded in verifier-anchor-erratum.md; four author packet anchors and originals unchanged.','limits':'Parent read complete REVIEW, FINAL, REPORT and READING-LIMITS; underlying source/primary/read/render identities bound without inherited semantic reading. Recovered truncations, AACK font loss/visual limits, unread scanned Waldhausen original, unread intermediates, incidental editorial exposure and guarded-history limits remain disclosed. Correctness remains UNDISCHARGED in contribution role.'}
for name,value in [('contribution-replay.json',out),('contribution-observed-root.json',before)]:
    p=P/name;p.write_text(json.dumps(value,indent=2)+'\n');p.chmod(0o600)
print(json.dumps(out,indent=2))
