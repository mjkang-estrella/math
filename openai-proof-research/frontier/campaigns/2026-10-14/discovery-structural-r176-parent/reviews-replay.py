#!/usr/bin/env python3
"""Read-only explicit-anchor intake of both notified S176A reviews."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2]
sp=importlib.util.spec_from_file_location('snapshot',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def main():
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert not tree['truncated'] and len(lookup)==13223
    for role in ['proof','contribution']:
        proof=role=='proof';root=B/('structural-r176-'+role+'-r1');out=O/(role+'-r1-adoption')
        anchors={'FINAL.md':'a6d04b8bfd76ea720fea5437ca1bd6ed51d792e09ba464ba9cb5df83159b75a7','private/packet/MANIFEST.json':'6ea49f5a68566d3dc1dd765614cd9f3d63fb9387de53d5850685851ffe1a7270','REPORT.md':'123c672464b7521c579767b9ba6f07c39a15ad7e58a3ed2f105bd85058c087a8'}if proof else{'FINAL.md':'4082498b7e85e8ffe9b593224f8b6ca37c9f9056c96bf6c692181767a1abaa9d','private/packet/MANIFEST.json':'74ee46c42d37a2aa0c88ed9f85e6d5f9669203418625d7b3c4bb9b1765aa021f','REPORT.md':'09c0aef79d5b5d03394e28efb51912799eda8a65d308f8b139d9a57bab1d58d5'}
        before=h.snap(root);mode=stat.S_IMODE(root.stat().st_mode);assert all(h.sha(root/p)==v for p,v in anchors.items())
        cmd=['python','-I','-B',str(root/'private/verify_packet.py'),'--root',str(root),'--final-sha',anchors['FINAL.md'],'--manifest-sha',anchors['private/packet/MANIFEST.json'],'--report-sha',anchors['REPORT.md']]
        if not proof:cmd+=['--project-root',str(P)]
        r=subprocess.run(cmd,cwd=P,text=True,capture_output=True,check=True);assert not r.stderr;result=json.loads(r.stdout);assert result['payload_files']==(49 if proof else 75)
        originals=read(root/('private/input-identities.json'if proof else'private/initial-input-bindings.json'));assert len(originals)==42;stable={}
        for x in originals:
            p=P/x['path'];expected=int(x['mode'],8)if isinstance(x['mode'],str)else x['mode'];assert h.sha(p)==x['sha256'] and p.stat().st_size==x['bytes'] and stat.S_IMODE(p.stat().st_mode)==expected;stable[x['path']]={'sha256':h.sha(p),'mode':expected}
        sections=read(root/('private/history-exact.json'if proof else'private/history/extents.json'));assert len(sections)==4
        for x in sections:
            p=P/x['original'if proof else'path'];expected=int(x['mode'],8)if isinstance(x['mode'],str)else x['mode'];assert h.sha(p)==x['whole_sha256'] and stat.S_IMODE(p.stat().st_mode)==expected
            with p.open('rb')as f:f.seek(x['start']);d=f.read(x['end']-x['start'])
            assert hashlib.sha256(d).hexdigest()==x['slice_sha256'if proof else'selected_sha256'];stable[p.relative_to(P).as_posix()]={'sha256':h.sha(p),'mode':expected}
        bindings=read(root/'private/source-binding.json')['verified_objects']if proof else read(root/'private/canonical-bindings.json');assert len(bindings)==9
        for x in bindings:
            path=x['path'if proof else'pinned_path'];e=lookup[path];assert e['size']==x['bytes'] and e['sha']==x['blob'if proof else'git_blob']
        if proof:
            for x in read(root/'private/selected-copies.json'):assert h.sha(P/x['original'])==h.sha(root/x['copy'])==x['sha256']
        assert h.snap(root)==before and stat.S_IMODE(root.stat().st_mode)==mode
        (out/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n')
        record={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'verifier_result':result,'artifact_only':True,'payload_files':49 if proof else 75,'canonical_objects':9,'unchanged_original_inputs':46,'stable_named_originals':stable,'entire_root_unchanged':True,'parent_semantic_reading':'Complete REVIEW/FINAL/REPORT, actual reading/isolation record and verifier; review bodies recovered by bounded halves after aggregate output truncation. A parent replay-script syntax typo was corrected before its first successful execution. Primary semantic extents remain attributed to reviewer; parent did not reread all primary proofs.'}
        (out/'replay.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({'role':role,'payload_files':record['payload_files'],'original_inputs':46,'entire_root_unchanged':True,'artifact_only':True}))
if __name__=='__main__':main()
