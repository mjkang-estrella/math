#!/usr/bin/env python3
"""Read-only Arithmetic147 frozen nominee intake; no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-arithmetic-discovery-r147'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def main():
    anchors={'FINAL.md':'1cbc7ce0973c54f7fed857a7f68e3adec14a3b8465d513ea058fd2bc2eebd96e','MANIFEST.json':'0980a026d7bea2327cad54df73a3d031cb5e9e10b43e12493ad8b12678f3e8ee','REPORT.md':'be8a12225b6040200542d820a23196d0fcab1a85eca3bda8613c35de25370aea'};frozen='aa34714980af05fbbed5ae223b73b8ec10c1b19d8865ff61fbf2615f582682a8';proof='5bead5a1ae6f45922b566ed0519198c4fe171d2cb301385d5cd75606dc2739f8'
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(A/n)==v for n,v in anchors.items())and sha(A/'THEOREM.md')==frozen and sha(A/'AUTHOR-PROOF.md')==proof
    cmd=['python','-I','-B',str(A/'verify_packet.py'),'--root',str(A),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md'],'--originals-project',str(P)];r=subprocess.run(cmd,cwd=P,text=True,capture_output=True,check=True);assert not r.stderr
    manifest=read(A/'MANIFEST.json');listed={x['path']for x in manifest['files']};actual={n for n,v in before.items()if v['kind']=='file'};assert len(listed)==83 and actual==listed|{'FINAL.md','MANIFEST.json','REPORT.md','ANCHORS.json'}
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert not tree['truncated']and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    bindings=read(A/'private/source-authentication.json');assert len(bindings)==8
    for x in bindings:
        p=A/'private/source'/Path(x['path']).name;data=p.read_bytes();e=lookup[x['path']];assert len(data)==x['bytes']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==x['blob']==e['sha']
    stable={};ranges=[]
    for x in read(A/'private/original-anchors.json'):
        p=P/x['path']
        with p.open('rb')as f:f.seek(x['start']);data=f.read(x['end']-x['start'])
        assert hashlib.sha256(data).hexdigest()==x['sha256'];ranges.append({'path':x['path'],'start':x['start'],'end':x['end'],'selection_sha256':x['sha256']})
        if x['start']==0 and x['end']==p.stat().st_size:stable[x['path']]=x['sha256']
    assert len(ranges)==15 and len(stable)==10 and snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode;dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'frozen_scope_sha256':frozen,'author_proof_sha256':proof,'artifact_only':True,'author_validator_stdout':r.stdout.strip(),'canonical_objects':8,'canonical_matches_complete_pinned_tree':True,'stable_named_originals':stable,'original_range_anchors':ranges,'whole_original_records':10,'original_slices':15,'completed_originals':7,'history_intervals':4,'entire_root_unchanged':True,'root_mode':mode,'payload_files':83,'outside_envelopes':4,'root_files':87,'parent_exact_membership_checked':True,'parent_semantic_reading':'Complete THEOREM/AUTHOR-PROOF/PREFREEZE/DERIVATIONS/UNRESOLVED/FINAL/REPORT/private READING/selection-limits and verifier. AUTHOR-PROOF read in overlapping [0,14500) and [14000,end) displays with full union and no truncation. Actual source/primary/history semantic reading remains attributed to author; parent authenticates bytes only.'};dump(O/'replay.json',report);print(json.dumps({'payload_files':83,'envelopes':4,'canonical_objects':8,'original_slices':15,'whole_originals':10,'author_unchanged':True,'artifact_only':True}))
if __name__=='__main__':main()
