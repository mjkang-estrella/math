#!/usr/bin/env python3
"""Read-only selected-packet intake for two notified results; no mathematical gate."""
import datetime, hashlib, importlib.util, json, os, stat, subprocess
from pathlib import Path
O=Path(__file__).resolve().parent; B=O.parent; P=B.parents[2]
def read(p): return json.loads(p.read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def snap(root):
    out={}
    def walk(d):
        for e in sorted(os.scandir(d),key=lambda e:e.name):
            p=Path(e.path); n=p.relative_to(root).as_posix(); st=p.lstat(); assert not e.is_symlink(),n
            if e.is_dir(follow_symlinks=False): out[n]={'kind':'directory','mode':stat.S_IMODE(st.st_mode)};walk(p)
            else:
                assert stat.S_ISREG(st.st_mode) and st.st_nlink==1,n
                out[n]={'kind':'file','mode':stat.S_IMODE(st.st_mode),'bytes':st.st_size,'sha256':sha(p),'nlink':st.st_nlink}
    walk(root); return out
def dump(p,d): p.write_text(json.dumps(d,indent=2)+'\n')
def verify(which):
    analytic=which=='analytic';root=B/('fresh-analytic-discovery-r168' if analytic else 'fresh-structural-discovery-r176');out=O if analytic else B/'discovery-structural-r176-parent'
    anchors=({'FINAL.md':'e28b104fddaaa29390b4a7433cbe0e20efaa5c8d180cafc9f0c3f08f6cbebaff','MANIFEST.json':'c5359c68732aae66948d9f033dfbaee2763608a8ce1c1a25d943130c2d7e2cb1','REPORT.md':'6ca0e1d252b38dc013c643de3b2709de3cc141ffe7cbd99af1144bd7dfb6c3d4'} if analytic else {'private/packet/FINAL.json':'4de09e5075185473eec343ebce26c306ef867830085e824a398ac2df23cddea3','private/packet/MANIFEST.json':'d72770adf400be4c9a85a18e632cf09570b79bce1f106b09e86a5193d34660b9','REPORT.md':'ab4ee4b1d783aa6f49267a265260a53a1bbcb57a24adbee29229b82c172bfe0c'})
    before=snap(root);mode=stat.S_IMODE(root.stat().st_mode);assert all(sha(root/n)==v for n,v in anchors.items())
    if analytic:
        cmd=['python','-I','-B',str(root/'verify_packet.py'),str(root),'--final',anchors['FINAL.md'],'--manifest',anchors['MANIFEST.json'],'--report',anchors['REPORT.md']]
    else:
        cmd=['python','-I','-B',str(root/'private/verify_packet.py'),'--root',str(root),'--final-sha',anchors['private/packet/FINAL.json'],'--manifest-sha',anchors['private/packet/MANIFEST.json'],'--report-sha',anchors['REPORT.md']]
    r=subprocess.run(cmd,cwd=P,text=True,capture_output=True,check=True); assert not r.stderr
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert not tree['truncated'] and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    bindings=read(root/('private/canonical-bindings.json' if analytic else 'private/canonical-objects.json'))
    for x in bindings:
        p=root/'private/canonical'/x['local'] if analytic else P/x['local'];d=p.read_bytes();e=lookup[x['path']]
        assert p.resolve().is_relative_to(root) and len(d)==x['bytes']==e['size'] and sha(p)==x['sha256'] and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['blob']==e['sha']
    stable={};closing={}
    if analytic:
        for i,x in enumerate(read(root/'private/original-extents.json')):
            p=P/x['path'];d=p.read_bytes();assert sha(p)==x['full_sha256'] and hashlib.sha256(d[x['start']:x['end']]).hexdigest()==x['section_sha256'] and d[x['start']:x['end']]==(root/f'private/original-section-{i}.txt').read_bytes();stable[x['path']]=sha(p)
        for x in read(root/'private/semantic-extents.json')['permitted_completed_exceptions']:
            p=P/x['path'];assert sha(p)==x['sha256_at_close'] and p.stat().st_size==x['bytes'];closing[x['path']]=sha(p)
    else:
        for x in read(root/'private/direct-anchors.json'):
            p=P/x['path'];assert sha(p)==x['sha256'] and p.stat().st_size==x['bytes'];stable[x['path']]=sha(p)
        for line in (root/'private/original-extents.jsonl').read_text().splitlines():
            x=json.loads(line);p=P/x['original'];d=p.read_bytes();assert len(d)==x['bytes'] and sha(p)==x['sha256'] and d[x['start']:x['end']]==(root/x['local']).read_bytes();stable[x['original']]=sha(p)
    assert snap(root)==before and stat.S_IMODE(root.stat().st_mode)==mode
    dump(out/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'artifact_only':True,'author_validator_stdout':r.stdout.strip(),'canonical_objects':len(bindings),'canonical_matches_complete_pinned_tree':True,'stable_named_originals':stable,'completed_original_closing_hashes_only':closing,'entire_root_unchanged':True,'root_mode':mode,'payload_files':58 if analytic else 62,'parent_semantic_reading':'A168 complete FINAL/REPORT/CALCULATIONS/DERIVATION/COMPARISON/OBSTRUCTION/READING-LIMITS/verifier; S176 complete STATEMENT/AUTHOR-PROOF/REPORT/reading-record/verifier/operative-comparison. Earlier oversized aggregate displays truncated; the proof and needed headers were recovered by bounded reads. Parent source/primary bodies not independently reread; child reading claims remain attributed.'}
    dump(out/'replay.json',report); print(json.dumps({'result':which,'payload_files':report['payload_files'],'canonical_objects':len(bindings),'unchanged':True,'artifact_only':True}))
if __name__=='__main__':
    verify('analytic');verify('structural')
