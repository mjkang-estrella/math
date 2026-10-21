#!/usr/bin/env python3
"""Read-only Arithmetic138 exact-packet authentication, not a mathematical gate."""
import importlib.util,json,stat,subprocess,hashlib
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];R=B/'fresh-arithmetic-discovery-r138'
sp=importlib.util.spec_from_file_location('identity',B/'discovery-analytic-r161-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_text())
def main():
    before=snap(R);mode=stat.S_IMODE(R.stat().st_mode);anchors={'FINAL.md':'3b3bf0475826b0ebcb26d0fe9542720752b96a28347a03a6ba86cbaee7bddc48','private/MANIFEST.json':'16fb1d03905325ac4d60bf12386bd02fdd296ecef54275dd0a84ff079f2479e5','REPORT.md':'2e6fff8cc4fef60310cca28cf103864f594c8997c02dc481c01533dc17b9ca23'}
    result=json.loads(subprocess.check_output(['python','-I','-B',str(R/'verify_packet.py'),'--root',str(R),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['private/MANIFEST.json'],'--report-sha256',anchors['REPORT.md']],cwd=P,text=True));assert result['payload_files']==76
    tree=read(P/'sources/preprints-tree.json');assert len(tree['tree'])==13223 and not tree['truncated'] and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';lookup={e['path']:e for e in tree['tree']};sources=read(R/'private/source-identities.json');companions=read(R/'private/companion-identities.json');assert len(sources)==23 and len(companions)==4
    for e in sources+companions:
        data=(P/e['local']).read_bytes();assert len(data)==e['bytes']==lookup[e['path']]['size'] and sha(P/e['local'])==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==lookup[e['path']]['sha']
    stable={}
    es=read(R/'private/completed-exception-extents.json');assert len(es)==6
    for e in es:
        p=P/e['path'];assert sha(p)==e['sha256'] and e['read_bytes']==[0,len(p.read_bytes())];stable[e['path']]=e['sha256']
    history=read(R/'private/history-selections.json');assert len(history)==5
    for e in history:
        data=(P/e['path']).read_bytes();lo,hi=e['bytes'];copy=R/'private'/e['local'];assert hashlib.sha256(data).hexdigest()==e['file_sha256'] and data[lo:hi]==copy.read_bytes() and sha(copy)==e['section_sha256'];stable[e['path']]=e['file_sha256']
    e=read(R/'private/history-late-selection.json');p=P/e['path'];assert len(p.read_bytes())==e['file_bytes'] and sha(p)==e['sha256'] and p.read_bytes()[e['start_byte']:e['end_byte']]==(R/'private/history-section-6.md').read_bytes() and sha(R/'private/history-section-6.md')==e['selection_sha256'];stable[e['path']]=e['sha256']
    assert snap(R)==before and stat.S_IMODE(R.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n');(O/'replay.json').write_text(json.dumps({'anchors':anchors,'verifier':result,'canonical_objects':23,'companion_objects':4,'completed_originals':6,'recorded_original_sections':6,'stable_named_originals':stable,'whole_root_unchanged':True,'artifact_checks_assign_no_mathematical_gate':True},indent=2)+'\n');print(json.dumps({'payload':76,'outside':4,'canonical':23,'companions':4,'completed_originals':6,'original_sections':6,'whole_root_unchanged':True}))
if __name__=='__main__':main()
