#!/usr/bin/env python3
"""Read-only S183N author intake; authentication assigns no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-structural-discovery-r183'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def main():
    anchors={'packet/FINAL.md':'d2e902a838b970c256bbbfe7da56ca9b4a39adee3c8cf3405d3e265bc70acb52','packet/MANIFEST.json':'cdea6c7a0e768749fa19b6fda8abf94604b3f7d03fb72cd3310a2423d8bdd354','REPORT.md':'fa1905c7b423787f61aa16612bfadd634630e49acef17b0e61b594172c55dab4'}
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(A/n)==v for n,v in anchors.items())
    frozen='31f7da24fdd8721b5a8d3e0bbc2083130e66ca9965eb1dc887ee9baa2d8efda0';proof='a0b55d5fcd8bc2406988a2b711c49725487b2600d5c74200034de1febc945163';assert sha(A/'FROZEN-THEOREM.md')==frozen and sha(A/'notes/03-author-proof.md')==proof and sha(A/'packet/FROZEN-THEOREM.md')==frozen and sha(A/'packet/notes/03-author-proof.md')==proof
    cmd=['python','-I','-B',str(A/'verify_packet.py'),'--packet',str(A/'packet'),'--report',str(A/'REPORT.md'),'--final-sha',anchors['packet/FINAL.md'],'--manifest-sha',anchors['packet/MANIFEST.json'],'--report-sha',anchors['REPORT.md']]
    r=subprocess.run(cmd,cwd=P,text=True,capture_output=True,check=True);assert not r.stderr
    manifest=read(A/'packet/MANIFEST.json');assert len(manifest['files'])==96;copies=[];packet_only=[]
    for x in manifest['files']:
        p=A/x['path']
        if p.is_file():assert p.read_bytes()==(A/'packet'/x['path']).read_bytes();copies.append(x['path'])
        else:packet_only.append(x['path'])
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert not tree['truncated']and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    bindings=read(A/'private/source-bindings.json');assert len(bindings)==12
    for x in bindings:
        p=P/x['local'];data=p.read_bytes();e=lookup[x['path']];assert p.resolve().is_relative_to(A)and len(data)==x['bytes']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==x['git_blob']==e['sha']
    stable={};ranges=[]
    for x in read(A/'private/completed-extents.json'):
        n=x['copy'];name=n.removeprefix('private/completed-').replace('__','/');p=B/name;assert p.stat().st_size==x['bytes']and sha(p)==x['sha256']and p.read_bytes()==(A/n).read_bytes();stable[p.relative_to(P).as_posix()]=x['sha256']
    for x in read(A/'private/history-extents.json'):
        p=P/x['path']
        with p.open('rb')as f:f.seek(x['start']);data=f.read(x['end']-x['start'])
        assert hashlib.sha256(data).hexdigest()==x['sha256']and data==(P/x['copy']).read_bytes();ranges.append({'path':x['path'],'start':x['start'],'end':x['end'],'selection_sha256':x['sha256']})
        if x['start']==0 and x['end']==p.stat().st_size:stable[x['path']]=x['sha256']
    assert len(stable)==6 and len(ranges)==3 and snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode;dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'frozen_scope_sha256':frozen,'author_proof_sha256':proof,'artifact_only':True,'author_validator_stdout':r.stdout.strip(),'canonical_objects':12,'canonical_matches_complete_pinned_tree':True,'stable_named_originals':stable,'original_range_anchors':ranges,'completed_originals':5,'selected_history_intervals':3,'whole_i88_hash_not_supplied_or_invented':True,'entire_root_unchanged':True,'root_mode':mode,'payload_files':96,'selected_working_copies_match':copies,'packet_only_members':packet_only,'wider_working_root_not_claimed_wholly_selected':True,'parent_semantic_reading':'Complete frozen theorem, FINAL/REPORT/frozen anchor, all four mathematical notes, READING-ISOLATION and verifier. Author proof read in overlapping [0,13500) and [13000,end) displays with full union and no truncation. Actual source/primary/history semantic reading remains attributed to author; parent authenticates bytes only.'};dump(O/'replay.json',report);print(json.dumps({'payload_files':96,'canonical_objects':12,'completed_originals':5,'history_intervals':3,'matching_working_copies':len(copies),'packet_only_members':packet_only,'author_unchanged':True,'artifact_only':True}))
if __name__=='__main__':main()
