#!/usr/bin/env python3
"""Read-only prefreeze packet authentication; no mathematical gate."""
import importlib.util,json,stat,subprocess,hashlib
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];R=B/'fresh-arithmetic-discovery-r137'
sp=importlib.util.spec_from_file_location('identity',B/'discovery-analytic-r161-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_text())
def main():
    before=snap(R);mode=stat.S_IMODE(R.stat().st_mode);anchors={'FINAL.md':'bcba24e324ed8003bdb25bbf59e94fd0258821818afcd8d70018cdf3122b000b','MANIFEST.json':'eca4a76d7b0110ad2b364f73ac64240fc5b6b2fba04908fadaa8f5342297b5ce','REPORT.md':'d3cc89e931c6a799fece043366f0ec16b9e68373f74a9a62ce565801ef4d09e0'}
    result=json.loads(subprocess.check_output(['python','-I','-B',str(R/'private/verify_packet.py'),'--root',str(R),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']],cwd=P,text=True));assert result['files']==65
    tree=read(P/'sources/preprints-tree.json');assert len(tree['tree'])==13223 and not tree['truncated'] and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';lookup={e['path']:e for e in tree['tree']};sources=read(R/'private/source-identities.json');assert len(sources)==12
    for e in sources:
        p=R/'private'/e['local'];data=p.read_bytes();assert sha(p)==e['sha256'] and len(data)==e['size']==lookup[e['path']]['size'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['sha']==lookup[e['path']]['sha']
    primaries=read(R/'private/primary-identities.json');assert len(primaries)==8
    for e in primaries:
        pdf=R/'private/primary'/(e['name']+'.pdf');txt=pdf.with_suffix('.txt');assert len(pdf.read_bytes())==e['bytes'] and sha(pdf)==e['sha256'] and sha(txt)==e['extract_sha256']
    stable={}
    for e in read(R/'private/original-comparisons.json'):assert e['matches'] and sha(P/e['path'])==e['expected_sha256']==e['current_sha256'];stable[e['path']]=e['expected_sha256']
    histories=read(R/'private/history-selections.json')+read(R/'private/late-history-selections.json');assert len(histories)==7
    for e in histories:
        data=(P/e['path']).read_bytes();lo,hi=e['extent_bytes']if 'extent_bytes'in e else(e['start'],e['end']);copy=e.get('local',e.get('copy'));assert hashlib.sha256(data).hexdigest()==e['full_sha256'] and data[lo:hi]==(P/copy).read_bytes() and sha(P/copy)==e['selected_sha256']
    assert snap(R)==before and stat.S_IMODE(R.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n');(O/'replay.json').write_text(json.dumps({'anchors':anchors,'verifier':result,'canonical_objects':12,'primary_pdf_text_pairs':8,'selected_original_history_sections':7,'stable_named_originals':stable,'whole_root_unchanged':True,'artifact_checks_assign_no_mathematical_gate':True},indent=2)+'\n');print(json.dumps({'artifact_replay':result,'canonical':12,'primary_pairs':8,'history_sections':7,'whole_root_unchanged':True}))
if __name__=='__main__':main()
