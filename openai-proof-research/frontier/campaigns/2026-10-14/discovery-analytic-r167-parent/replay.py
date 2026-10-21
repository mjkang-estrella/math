#!/usr/bin/env python3
"""Read-only selected-packet and full-root membership authentication."""
import importlib.util,json,stat,subprocess,hashlib
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];R=B/'fresh-analytic-discovery-r167'
sp=importlib.util.spec_from_file_location('identity',B/'discovery-analytic-r161-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_text())
def main():
    before=snap(R);mode=stat.S_IMODE(R.stat().st_mode);anchors={'FINAL.md':'0b23a68d62f4a6a433391c7e75d4ec2f6b3d6c23726cf688cc39f305f39db132','MANIFEST.json':'fcd7bcc27077f4e78ec8130728b25d6512256b0e8f7a1a88142c64d5a6f5a48b','REPORT.md':'043ce8f7ec71946cccf8332165d07965fa10ab6d63b6214192c4b96e1df82a40'}
    result=subprocess.check_output(['python','-I','-B',str(R/'verify_packet.py'),'--root',str(R),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']],cwd=P,text=True);assert '77 selected files'in result
    m=read(R/'MANIFEST.json');names={e['path']for e in m['files']};assert len(names)==len(m['files'])==77 and {p for p,e in before.items()if e['kind']=='file'}==names|{'MANIFEST.json','REPORT.md','ANCHORS.json'}
    tree=read(P/'sources/preprints-tree.json');assert len(tree['tree'])==13223 and not tree['truncated'] and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';lookup={e['path']:e for e in tree['tree']};sources=read(R/'private/acquisitions.json');assert len(sources)==33
    for e in sources:
        data=(P/e['local']).read_bytes();assert len(data)==e['size']==lookup[e['path']]['size'] and sha(P/e['local'])==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['sha']==lookup[e['path']]['sha']
    stable={}
    for e in read(R/'private/completed-originals.json'):assert sha(P/e['path'])==e['sha256'] and len((P/e['path']).read_bytes())==e['bytes'];stable[e['path']]=e['sha256']
    histories=sum((read(R/'private'/n)for n in ['original-extents.json','quadratic-original-extents.json','late-original-extents.json']),[]);assert len(histories)==12
    for e in histories:
        path=e.get('original',e.get('path'));data=(P/path).read_bytes();expected=e.get('whole_sha256',e.get('source_sha256'));assert hashlib.sha256(data).hexdigest()==expected and data[e['start']:e['end']]==(P/e.get('local',e.get('copy'))).read_bytes();stable[path]=expected
    assert snap(R)==before and stat.S_IMODE(R.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n');(O/'replay.json').write_text(json.dumps({'anchors':anchors,'verifier_stdout':result.strip(),'selected_payload_files':77,'outside_envelopes':3,'parent_exact_file_membership_matches':True,'canonical_objects':33,'completed_originals':9,'recorded_original_extents':12,'stable_named_originals':stable,'whole_root_unchanged':True,'artifact_checks_assign_no_mathematical_gate':True},indent=2)+'\n');print(json.dumps({'selected_payload':77,'outside_envelopes':3,'canonical':33,'completed_originals':9,'recorded_original_extents':12,'whole_root_unchanged':True}))
if __name__=='__main__':main()
