#!/usr/bin/env python3
"""Read-only S238 packet/provenance replay; copied controls are temporary."""
from pathlib import Path, PurePosixPath
import datetime, hashlib, json, os, re, runpy, stat, tempfile

P = Path(__file__).resolve().parent
A = P.parent / 'fresh-structural-discovery-r238'
K = A / 'packet'
C = P.parents[1]
PROJECT = C.parents[2]
sha = lambda b: hashlib.sha256(b).hexdigest()
read = lambda p: json.loads(p.read_bytes())
anchors = {
    'packet/FINAL.md': 'ff7743cf6b6914964c5b4e6aca019d1118073f04d9b8438a712d713059f64494',
    'packet/MANIFEST.json': '92eeba044303f5ac201f709cf4bbf529c43a9e354379aad331d69c394a07a242',
    'REPORT.md': '908c9285b3b13aaa0068154a7090be87028370cc9dd57f1576c9253ffc55ef8c',
}
def inventory(root):
    result = {}
    for p in [root, *sorted(root.rglob('*'))]:
        assert not p.is_symlink()
        mode = oct(stat.S_IMODE(p.stat().st_mode))
        name = p.relative_to(root).as_posix()
        if p.is_dir(): result[name] = {'type': 'dir', 'mode': mode}
        else:
            assert p.is_file()
            b = p.read_bytes()
            result[name] = {'type': 'file', 'mode': mode, 'bytes': len(b), 'sha256': sha(b)}
    return result
before = inventory(A)
for n, h in anchors.items(): assert sha((A/n).read_bytes()) == h
vb = (K/'verify_packet.py').read_bytes()
assert sha(vb) == 'f199f6a5d3a452b1dd1514356d2c925683a41062e010d9d77b3dd019c0fd46ab'
verify = runpy.run_path(str(K/'verify_packet.py'))['verify']
verified = verify(K, anchors['packet/MANIFEST.json'], anchors['packet/FINAL.md'], A/'REPORT.md', anchors['REPORT.md'])
m = read(K/'MANIFEST.json')
for item in m['directories']:
    name = item['path']; q = PurePosixPath(name)
    assert not q.is_absolute() and '..' not in q.parts
selected = {x['path'] for x in m['files']}
assert len(selected) == 79 and len(m['directories']) == 14
for n in ['AUTHOR-PROOF.md','COMPARISON.md','FINAL.md','FROZEN.md','PREFREEZE.md','READING-LIMITS.md','frozen-anchor.json','verify_packet.py']:
    assert (A/n).read_bytes() == (K/n).read_bytes()
assert sha((K/'FROZEN.md').read_bytes()) == '1e4dbb6345bf6f0c61bb589b394e6454f382f329f87eddbd3a91b1e18ce2f212'
assert sha((K/'AUTHOR-PROOF.md').read_bytes()) == 'c2faa9dfe4e993cd299503b7b5d365653e866742dc6df6560fe864d30727d654'

tree_bytes = (PROJECT/'sources/preprints-tree.json').read_bytes()
assert len(tree_bytes) == 4858136 and sha(tree_bytes) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree = json.loads(tree_bytes)
entries = tree['tree'] if isinstance(tree, dict) else tree
assert len(entries) == 13223
sel = read(K/'private/tree-selection.json')
actual = [x for x in entries if 'boltzmann' in x['path'].casefold() and 'nonuniqueness' in x['path'].casefold()]
assert sel == actual and len(sel) == 43
by_path = {x['path']: x for x in sel}
auth = read(K/'private/canonical-auth.json')
assert len(auth) == 35 and {x['path'] for x in auth} == {x['path'] for x in sel if x['type']=='blob'}
for x in auth:
    b = (K/'private/canonical'/x['path']).read_bytes()
    blob = hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    assert len(b)==x['bytes'] and sha(b)==x['sha256'] and blob==x['git_blob']==by_path[x['path']]['sha']

reads = [json.loads(x) for x in (K/'private/semantic-reads.jsonl').read_bytes().splitlines()]
for x in reads:
    b = (K/'private/canonical'/x['path']).read_bytes(); lines=b.splitlines(keepends=True)
    lo,hi=x['lines']; assert 1<=lo<=hi<=len(lines)
    assert x['bytes']==[sum(map(len,lines[:lo-1])),sum(map(len,lines[:hi]))]
    assert sha(b)==x['sha256'] and all(lo<=i<=hi for i in x['masked_lines'])
coverage=read(K/'private/source-coverage.json')
assert len(coverage)==31
for x in coverage:
    b=(K/'private/canonical'/x['path']).read_bytes(); lines=b.splitlines(keepends=True)
    assert len(lines)==x['line_count']
    chosen=set()
    for lo,hi in x['display_selections']: chosen.update(range(lo,hi+1))
    assert sorted(set(range(1,len(lines)+1))-chosen)==x['unselected_lines']==[]
    recorded=set()
    for r in reads:
        if r['path']==x['path']: recorded.update(range(r['lines'][0],r['lines'][1]+1))
    assert chosen<=recorded

pr=K/'private/primary'
primary_reads=[json.loads(x) for x in (pr/'reads.jsonl').read_bytes().splitlines()]
for x in primary_reads:
    b=(pr/(x['id']+'.txt')).read_bytes(); lines=b.splitlines(keepends=True)
    lo=x['line_start'];hi=x['line_end_inclusive']
    assert sha(b)==x['source_sha256'] and 1<=lo<=hi<=len(lines)
    assert (x['byte_start'],x['byte_end_exclusive'])==(sum(map(len,lines[:lo-1])),sum(map(len,lines[:hi])))
    assert all(lo<=i<=hi for i in x['masked_running_headers'])
pdfs=[]
for x in read(pr/'access.json'):
    if 'failure' in x or x['id']=='MW1999': continue
    b=(pr/(x['id']+'.pdf')).read_bytes();tb=(pr/(x['id']+'.txt')).read_bytes()
    assert len(b)==x['bytes'] and sha(b)==x['sha256'] and len(tb)==x['text_bytes']
    assert len(tb.splitlines(keepends=True))==x['lines']
    pdfs.append(x['id'])
for metadata,stem in [('BGL-access.json','BGL-near'),('GPV-access.json','GPV2009'),('Golse-access.json','Golse2005')]:
    x=read(pr/metadata);b=(pr/(stem+'.pdf')).read_bytes()
    assert len(b)==x['bytes'] and sha(b)==x['sha256'];pdfs.append(stem)
assert len(pdfs)==7
assert sha((K/'private/lean-363.md').read_bytes())=='2e3c36a9e6f7dca7922734f496559271cef40ffc36e63afb95da8a55ffe35304'
formal=read(K/'private/lean-access.json');fb=(K/'private/lean-BoltzmannNonuniqueness.lean').read_bytes()
assert len(fb)==formal['bytes'] and sha(fb)==formal['sha256'] and b'sorry' in fb
guards=read(K/'private/guards.json')
brief=(C/'expanded-target-2026-10-17/fresh-structural-r220-isolated-r238-brief.txt').read_text()
patterns=set(re.findall(r'\*[A-Za-z0-9][A-Za-z0-9*_-]*\*',brief))
assert len(patterns)==399 and set(guards['wildcards'])==patterns and len(guards['substrings'])==162
assert all(s in brief for s in guards['substrings'])
history=read(K/'private/original-navigation.json');assert history['hits']==[]

controls=[]
with tempfile.TemporaryDirectory(prefix='tiny-controls-',dir=P) as td:
    root=Path(td)/'packet';root.mkdir();report=Path(td)/'REPORT.md';report.write_bytes(b'control report\n')
    f=root/'FINAL.md';f.write_bytes(b'control final\n');os.chmod(f,0o444)
    tiny={'schema':'structural238-exact-packet-v1','manifest_mode':'0444','directories':[{'path':'.','mode':oct(stat.S_IMODE(root.stat().st_mode))}],
          'files':[{'path':'FINAL.md','bytes':len(f.read_bytes()),'sha256':sha(f.read_bytes()),'mode':'0444'}]}
    mf=root/'MANIFEST.json';mf.write_text(json.dumps(tiny));os.chmod(mf,0o444)
    args=(root,sha(mf.read_bytes()),sha(f.read_bytes()),report,sha(report.read_bytes()))
    controls.append({'case':'intact','accepted':verify(*args)['verified']})
    def reject(label,args=args):
        try: verify(*args)
        except AssertionError as e: controls.append({'case':label,'rejected':True,'reason':str(e)})
        else: raise AssertionError('Control accepted: '+label)
    saved=f.read_bytes();os.chmod(f,0o644);f.write_bytes(saved+b'X');os.chmod(f,0o444);reject('changed bytes')
    os.chmod(f,0o644);f.write_bytes(saved);reject('changed mode');os.chmod(f,0o444)
    (root/'extra').write_bytes(b'x');reject('extra file');(root/'extra').unlink()
    (root/'extra-dir').mkdir();reject('extra directory');(root/'extra-dir').rmdir()
    f.rename(root/'missing');reject('omitted file');(root/'missing').rename(f)
    reject('wrong detached REPORT anchor',args[:-1]+('0'*64,))
    controls.append({'case':'restored','accepted':verify(*args)['verified']})

after=inventory(A);assert after==before
(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'packet_verification':verified,
     'packet_files_including_manifest':80,'admitted_files_for_review':83,'whole_author_files':sum(x['type']=='file'for x in before.values()),
     'whole_author_directories_including_root':sum(x['type']=='dir'for x in before.values()),'whole_author_bytes_and_modes_unchanged':True,
     'canonical_blobs_authenticated':len(auth),'canonical_tree_entries':len(sel),'canonical_semantic_intervals_bound':len(reads),
     'complete_source_file_selections_bound':len(coverage),'primary_intervals_bound':len(primary_reads),'primary_pdf_receipts_bound':len(pdfs),
     'formal_identities_bound':2,'proved_formal_support':False,'history_passes':1,'history_bodies_admitted':0,
     'guards':{'wildcards':399,'substrings':162},'tiny_copied_controls':controls,
     'mathematical_scope':'Artifact/provenance replay only; author selection logs do not establish parent semantic reading or correctness.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
