#!/usr/bin/env python3
"""Read-only Analytic176 intake; authentication assigns no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-analytic-discovery-r176'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def main():
    anchors={'FINAL.md':'0bdcc12b588e63196f4e38dfd70d6e31f417919b076346454b73fa5acd406f69','MANIFEST.json':'0b56d9bccbe9e31d6d6cbfd4e8d1adad73edad599090ef47096f099db0b6b89d','REPORT.json':'ac106f7f2b10ad82c9617e0df5f360e086cd8cb0bb5234d126b8eccc6c333246'}
    receipt=read(O/'terminal-anchor-receipt.json');assert not receipt['textTruncated']and receipt['nextTextOffset']is None and receipt['position']==188 and all(v in receipt['text']for v in anchors.values())
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(A/n)==v for n,v in anchors.items())
    cmd=['python','-I','-B',str(A/'verify_packet.py'),'--root',str(A),'--final',anchors['FINAL.md'],'--manifest',anchors['MANIFEST.json'],'--report',anchors['REPORT.json']];r=subprocess.run(cmd,cwd=P,text=True,capture_output=True,check=True);assert not r.stderr
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert not tree['truncated']and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    bindings=read(A/'private/source-authentication.json');assert len(bindings)==18
    for x in bindings:
        p=P/x['local'];data=p.read_bytes();e=lookup[x['path']];assert p.resolve().is_relative_to(A)and len(data)==x['bytes']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==x['git_blob']==e['sha']
    stable={};ranges=[]
    for x in read(A/'private/completed-extents.json'):
        p=P/x['path'];start,end=x['bytes'];assert start==0 and end==p.stat().st_size and sha(p)==x['sha256'];stable[x['path']]=x['sha256'];n='private/completed175-'+x['path'].removeprefix(B.relative_to(P).as_posix()+'/').replace('/','--');assert p.read_bytes()==(A/n).read_bytes()
    copies=['private/i07-structures-selected.md','private/i02-operator-r2-selected.md']
    for x,n in zip(read(A/'private/original-extents.json'),copies):
        with(P/x['path']).open('rb')as f:f.seek(x['start']);data=f.read(x['end']-x['start'])
        assert hashlib.sha256(data).hexdigest()==x['sha256']and data==(A/n).read_bytes();ranges.append({'path':x['path'],'start':x['start'],'end':x['end'],'selection_sha256':x['sha256']})
    assert len(stable)==8 and len(ranges)==2 and snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode;dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'anchor_provenance':'Untruncated earlier full final handoff at position188 of the same completed child turn, recovered because published task summary was the later short closing message.','artifact_only':True,'author_validator_stdout':r.stdout.strip(),'canonical_objects':18,'canonical_matches_complete_pinned_tree':True,'stable_named_originals':stable,'original_range_anchors':ranges,'whole_history_hashes_not_supplied_or_invented':True,'entire_root_unchanged':True,'root_mode':mode,'payload_files':80,'outside_envelopes':4,'total_files':sum(v['kind']=='file'for v in before.values()),'parent_semantic_reading':'Complete FINAL/REPORT/INTERFACES/HOLONOMY/ANNULAR/COMPARISON/private READING-LIMITS and verifier. Initial combined completed-child history/file display exceeded the orchestration output budget; all needed file bodies and metadata were recovered in separate bounded displays. Actual source/primary/history semantic reading remains attributed to author; parent authenticates bytes only.'};assert report['total_files']==84;dump(O/'replay.json',report);print(json.dumps({'payload_files':80,'envelopes':4,'canonical_objects':18,'completed_originals':8,'history_intervals':2,'unchanged':True,'artifact_only':True}))
if __name__=='__main__':main()
