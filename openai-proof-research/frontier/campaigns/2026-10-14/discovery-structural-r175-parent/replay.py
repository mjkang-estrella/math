#!/usr/bin/env python3
"""Read-only Structural175 exact-packet authentication, no mathematical gate."""
import importlib.util,json,stat,subprocess,hashlib
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];R=B/'fresh-structural-discovery-r175'
sp=importlib.util.spec_from_file_location('identity',B/'discovery-analytic-r161-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_text())
def main():
    before=snap(R);mode=stat.S_IMODE(R.stat().st_mode);anchors={'private/packet/FINAL.json':'2fe691e8ef4f7924fc56d86f76a22e2b465187223e15e69967d57e486daf812e','private/packet/MANIFEST.json':'6b8934c49408edc01dc2c7346c9fba2254b9931c9aefb732ea1eb511f833b03e','REPORT.md':'7779ca988834b3862c200b9602d62a365db3dff3e9db442aee4a03c9cb2f9397'}
    result=subprocess.check_output(['python','-I','-B',str(R/'private/verify_packet.py'),'--root',str(R),'--manifest',str(R/'private/packet/MANIFEST.json'),'--final',str(R/'private/packet/FINAL.json'),'--report',str(R/'REPORT.md'),'--manifest-sha256',anchors['private/packet/MANIFEST.json'],'--final-sha256',anchors['private/packet/FINAL.json'],'--report-sha256',anchors['REPORT.md']],cwd=P,text=True);assert '85 members'in result
    tree=read(P/'sources/preprints-tree.json');assert len(tree['tree'])==13223 and not tree['truncated'] and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';lookup={e['path']:e for e in tree['tree']};sources=read(R/'private/canonical-objects.json');assert len(sources)==13
    for e in sources:
        data=(R/'private'/e['local']).read_bytes();assert len(data)==e['bytes']==lookup[e['path']]['size'] and sha(R/'private'/e['local'])==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==lookup[e['path']]['sha']
    stable={}
    for e in read(R/'private/direct-anchors.json'):
        if e['path']=='frontier/NEW-TEN-2026-10-14.md':continue
        assert sha(P/e['path'])==e['sha256'];stable[e['path']]=e['sha256']
    histories=read(R/'private/original-sections.json')+read(R/'private/original-sections-late.json');assert len(histories)==8
    for e in histories:
        name=e.get('original',e.get('path'));data=(P/name).read_bytes();copy=R/e['local']if e['local'].startswith('private/')else R/'private'/e['local'];assert hashlib.sha256(data).hexdigest()==e['sha256'] and data[e['start']:e['end']]==copy.read_bytes();stable[name]=e['sha256']
    assert snap(R)==before and stat.S_IMODE(R.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n');(O/'replay.json').write_text(json.dumps({'anchors':anchors,'verifier_stdout':result.strip(),'payload_files':85,'outside_envelopes':3,'canonical_objects':13,'direct_identity_records':11,'recorded_original_sections':8,'stable_named_originals':stable,'whole_root_unchanged':True,'artifact_checks_assign_no_mathematical_gate':True},indent=2)+'\n');print(json.dumps({'payload':85,'outside':3,'canonical':13,'direct_records':11,'original_sections':8,'whole_root_unchanged':True}))
if __name__=='__main__':main()
