#!/usr/bin/env python3
"""Read-only exact selected contribution-review authentication, not correctness."""
import importlib.util,json,stat,subprocess,hashlib
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parents[1];P=B.parents[2];R=B/'analytic-r166-contribution-r1'
sp=importlib.util.spec_from_file_location('identity',B/'discovery-analytic-r161-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_text())
def main():
    before=snap(R);mode=stat.S_IMODE(R.stat().st_mode);anchors={'FINAL.md':'173a0841322cdd9a1fc47a09479aca77b06dae8fe8d041593547b88aa1787790','private/MANIFEST.json':'220d045f055b86dc59f9e8d5502d8efc9d350b4b1affa097a301d4de0ab563dd','REPORT.md':'732433b62390020bdaf0bf465ec55c05c7bd72e17dbce55cfb91e2441620474f'}
    result=json.loads(subprocess.check_output(['python','-I','-B',str(R/'private/verify_review.py'),'--root',str(R),'--final',anchors['FINAL.md'],'--manifest',anchors['private/MANIFEST.json'],'--report',anchors['REPORT.md']],cwd=P,text=True));assert result['selected_files']==58
    selected=read(R/'private/selected-inputs.json');assert len(selected)==30;stable={}
    for e in selected:
        p=P/e['original'];data=p.read_bytes()
        if 'start'in e:data=data[e['start']:e['end']]
        else:assert len(data)==e['bytes'] and oct(stat.S_IMODE(p.stat().st_mode))==e['original_mode'];stable[e['original']]=e['sha256']
        assert hashlib.sha256(data).hexdigest()==e['sha256'] and data==(R/e['selected']).read_bytes()
    tree=read(P/'sources/preprints-tree.json');assert len(tree['tree'])==13223 and not tree['truncated'] and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';lookup={e['path']:e for e in tree['tree']};canonical=read(R/'private/canonical-selected.json');assert len(canonical)==9
    for e in canonical:
        assert lookup[e['path']]['sha']==e['git_blob'] and lookup[e['path']]['size']==e['bytes'];data=next((R/x['selected']).read_bytes()for x in selected if x['sha256']==e['sha256']);assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']
    for e in read(R/'private/initial-anchors.json'):assert sha(P/e['path'])==e['sha256'] and len((P/e['path']).read_bytes())==e['bytes'] and oct(stat.S_IMODE((P/e['path']).stat().st_mode))==e['mode']
    assert snap(B/'fresh-analytic-discovery-r166')==read(B/'discovery-analytic-r166-parent/observed-root.json')['root'] and snap(R)==before and stat.S_IMODE(R.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n');(O/'replay.json').write_text(json.dumps({'anchors':anchors,'verifier':result,'canonical_objects':9,'selected_original_inputs_and_extents':30,'stable_named_originals':stable,'author_whole_root_unchanged':True,'review_whole_root_unchanged':True,'mathematical_correctness_verdict':None},indent=2)+'\n');print(json.dumps({'artifact_replay':result,'canonical':9,'selected_inputs_and_extents':30,'author_unchanged':True}))
if __name__=='__main__':main()
