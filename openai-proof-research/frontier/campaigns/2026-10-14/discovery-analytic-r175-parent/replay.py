#!/usr/bin/env python3
"""Read-only Analytic175 intake; authentication assigns no mathematical gate."""
import datetime, hashlib, importlib.util, json, stat, subprocess
from pathlib import Path
O=Path(__file__).resolve().parent; B=O.parent; P=B.parents[2]; A=B/'fresh-analytic-discovery-r175'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha; snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def main():
    anchors={'FINAL.md':'b3f45f187bb8303de640ffbc80b261912fea33fc109199f43c47649a25fe994a','MANIFEST.json':'20d8b03e3d9a54e8c069b4b140d81192898dd219f4cb4906ec68c91750652478','REPORT.json':'b410d433066931f51be4885f6b195abfcf530014c4daed9fc2c6394e141e5c45'}
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(A/n)==v for n,v in anchors.items())
    cmd=['python','-I','-B',str(A/'verify_packet.py'),'--root',str(A),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.json']]
    r=subprocess.run(cmd,cwd=P,text=True,capture_output=True,check=True);assert not r.stderr
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert not tree['truncated'] and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    bindings=read(A/'private/source-authentication.json');assert len(bindings)==15
    for x in bindings:
        p=P/x['local'];data=p.read_bytes();e=lookup[x['path']];assert p.resolve().is_relative_to(A) and len(data)==x['size']==e['size'] and sha(p)==x['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==x['sha']==e['sha']
    stable={}
    for x in read(A/'private/exception-reads.json'):
        p=P/x['path'];assert sha(p)==x['sha256'] and p.stat().st_size==x['bytes'];stable[x['path']]=x['sha256']
    ranges=[]
    for x in read(A/'private/selected-history-extents.json'):
        with(P/x['path']).open('rb')as f:f.seek(x['start']);data=f.read(x['end']-x['start'])
        assert hashlib.sha256(data).hexdigest()==x['sha256'] and data==(P/x['destination']).read_bytes()
        ranges.append({'path':x['path'],'start':x['start'],'end':x['end'],'selection_sha256':x['sha256']})
    assert len(stable)==9 and len(ranges)==7 and snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'artifact_only':True,'author_validator_stdout':r.stdout.strip(),'canonical_objects':len(bindings),'canonical_matches_complete_pinned_tree':True,'stable_named_originals':stable,'original_range_anchors':ranges,'whole_history_hashes_not_supplied_or_invented':True,'entire_root_unchanged':True,'root_mode':mode,'payload_files':65,'outside_envelopes':4,'total_files':sum(v['kind']=='file'for v in before.values()),'parent_semantic_reading':'Complete FINAL/REPORT/CARRIER/ALGEBRA/OPERATION/COMPARISON/INTERFACES/private READING-LIMITS and verifier read in the preceding continuous intake. Source/primary/history actual semantic reading remains attributed to author; parent authenticates bytes only. Parent orchestration displays were oversized/truncated; needed coordination fields and selected model descriptors recovered by bounded selections, no mathematical proof inferred from truncated output.'}
    assert report['total_files']==69;dump(O/'replay.json',report);print(json.dumps({'payload_files':65,'envelopes':4,'canonical_objects':15,'completed_originals':9,'history_intervals':7,'unchanged':True,'artifact_only':True}))
if __name__=='__main__':main()
