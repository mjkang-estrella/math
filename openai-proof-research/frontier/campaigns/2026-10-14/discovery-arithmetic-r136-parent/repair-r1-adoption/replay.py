#!/usr/bin/env python3
"""Read-only replay of the completed first exact-scope repair; no mathematical gates."""
import hashlib, importlib.util, json, stat, subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parents[1];P=B.parents[2];R=B/'arithmetic-r136-repair-r1'
sp=importlib.util.spec_from_file_location('identity',B/'discovery-analytic-r161-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_text())
def main():
    before=snap(R); mode=stat.S_IMODE(R.stat().st_mode)
    anchors={'FINAL.md':'e5706a6640bb8e0b23a3d66e9f0be0c57b13769e35dbf4c2ace56512f2517466','MANIFEST.json':'443db69e58c1ddfd5b94e8a47bd883cd4b5ee9eeff61def48dd57a158bc7aeb8','REPORT.md':'a54028a1099021fc27769daae8bbddae5689e289729f583269a01da54f0a6fdb'}
    result=subprocess.check_output(['python','-I','-B',str(R/'verify_packet.py'),'--root',str(R),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']],cwd=P,text=True)
    verified=json.loads(result);assert verified['payload_files']==83 and verified['exact_directories']==13
    selected=read(R/'private/selected-input-identities.json');assert len(selected)==58
    for e in selected:
        p=P/e['original'];c=R/e['copy'];assert len(p.read_bytes())==e['bytes'] and sha(p)==e['sha256']==sha(c) and oct(stat.S_IMODE(p.stat().st_mode))==e['mode']
    history=read(R/'private/history-authentication.json');assert len(history)==2
    for e in history:
        p=P/e['path'];data=p.read_bytes();lo,hi=e['bytes'];assert len(data)==e['total'] and sha(p)==e['sha256'] and hashlib.sha256(data[lo:hi]).hexdigest()==e['selected_sha256'] and (P/e['copy']).read_bytes()==data[lo:hi] and oct(stat.S_IMODE(p.stat().st_mode))==e['mode']
    tree=read(P/'sources/preprints-tree.json');assert len(tree['tree'])==13223 and not tree['truncated'] and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';entries={e['path']:e for e in tree['tree']}
    sources=read(R/'private/source-authentication.json');assert len(sources)==9
    for e in sources:
        p=R/e['copy'];data=p.read_bytes();blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest();assert sha(p)==e['sha256'] and blob==e['git_blob']==entries[e['tree_path']]['sha'] and len(data)==entries[e['tree_path']]['size']
    primary=read(R/'private/primary-authentication.json');assert len(primary)==26
    for e in primary:
        if 'file' in e:
            p=R/e['file'];assert sha(p)==e['sha256'] and len(p.read_bytes())==e['bytes']
        else:
            assert e['matches_supplied_text'] and sha(R/'private/primary'/f"{e['fresh_extraction']}.txt")==e['text_sha256']
    math=json.loads(subprocess.check_output(['python','-I','-B',str(R/'private/verify_mathematics.py')],cwd=P,text=True));assert math==read(R/'private/mathematics-checks.json') and math['pell_seed']['B_is_fixed']==22
    closed=[]
    a=B/'discovery-arithmetic-r136-parent';c=B/'discovery-analytic-r161-parent'
    for root,record in [('fresh-arithmetic-discovery-r136',a),('arithmetic-r136-proof-r1',a/'proof-r1-adoption'),('arithmetic-r136-contribution-r1',a/'contribution-r1-adoption'),('fresh-analytic-discovery-r161',c),('analytic-r161-proof-r1',c/'proof-r1-adoption'),('analytic-r161-contribution-r1',c/'contribution-r1-adoption')]:
        assert snap(B/root)==read(record/'observed-root.json')['root'];closed.append(root)
    assert snap(R)==before and stat.S_IMODE(R.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n')
    (O/'replay.json').write_text(json.dumps({'anchors':anchors,'verifier':verified,'selected_original_inputs':58,'selected_original_history_sections':2,'canonical_objects':9,'primary_fixture_and_fresh_extract_identities':26,'finite_mathematics_receipt_matches':True,'fixed_B_only':22,'sealed_closed_roots_unchanged':closed,'root_unchanged_after_replay':True,'mathematical_gate_assigned':False},indent=2)+'\n')
    print(json.dumps({'artifact_replay':'matched','payload':83,'envelopes':4,'directories':13,'unchanged_original_inputs_and_history':60,'mathematical_gate':False}))
if __name__=='__main__':main()
