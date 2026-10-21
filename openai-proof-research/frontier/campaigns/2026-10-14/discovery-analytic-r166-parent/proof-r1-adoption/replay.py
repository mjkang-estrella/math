#!/usr/bin/env python3
"""Read-only exact selected correctness-review authentication."""
import importlib.util,json,stat,subprocess,hashlib
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parents[1];P=B.parents[2];R=B/'analytic-r166-proof-r1'
sp=importlib.util.spec_from_file_location('identity',B/'discovery-analytic-r161-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_text())
def main():
    before=snap(R);mode=stat.S_IMODE(R.stat().st_mode);anchors={'FINAL.md':'5a2535ab5ef8112a2db7e53e8fa88c0579289f052631d41ab62ac94cd31f8d4d','private/MANIFEST.json':'9d87c577f880beba1a560f3a737b1da097b143b588c880de345d67a73e84d5f8','REPORT.md':'66997fb075855b8bab34cb9bd860dddca76eefed3049c608cf08b34fe06f0b6e'}
    result=json.loads(subprocess.check_output(['python','-I','-B',str(R/'private/verify_review.py'),'--final-sha',anchors['FINAL.md'],'--manifest-sha',anchors['private/MANIFEST.json'],'--report-sha',anchors['REPORT.md']],cwd=P,text=True));assert result['files']==68
    selected=read(R/'private/selected-inputs.json');assert len(selected)==43;stable={};bounded=[]
    for e in selected:
        name=e.get('original',e.get('local'));p=P/name
        if 'semantic_extent'in e:
            lo,hi=e['semantic_extent']
            with p.open('rb')as f:f.seek(lo);data=f.read(hi-lo)
            bounded.append({'path':name,'start':lo,'end':hi,'sha256':e['sha256']})
        else:data=p.read_bytes();stable[name]=e['sha256']
        assert len(data)==e['bytes'] and hashlib.sha256(data).hexdigest()==e['sha256'] and data==(R/e['selected']).read_bytes()
        if 'mode'in e:assert oct(stat.S_IMODE(p.stat().st_mode))==e['mode']
        if 'original_sha256'in e:assert sha(p)==e['original_sha256'];stable[name]=e['original_sha256']
    tree=read(P/'sources/preprints-tree.json');assert len(tree['tree'])==13223 and not tree['truncated'] and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';lookup={e['path']:e for e in tree['tree']};canonical=[e for e in selected if 'git_blob'in e];assert len(canonical)==9
    for e in canonical:
        data=(R/e['selected']).read_bytes();assert lookup[e['path']]['sha']==e['git_blob'] and lookup[e['path']]['size']==len(data) and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']
    author=B/'discovery-analytic-r166-parent'
    for root,record in [('fresh-analytic-discovery-r166',author),('analytic-r166-contribution-r1',author/'contribution-r1-adoption')]:assert snap(B/root)==read(record/'observed-root.json')['root']
    assert snap(R)==before and stat.S_IMODE(R.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n');(O/'replay.json').write_text(json.dumps({'anchors':anchors,'verifier':result,'canonical_objects':9,'selected_original_inputs_and_extents':43,'stable_named_originals':stable,'bounded_original_extents':bounded,'author_and_contribution_review_whole_roots_unchanged':True,'review_whole_root_unchanged':True,'artifact_checks_assign_no_mathematical_gate':True},indent=2)+'\n');print(json.dumps({'artifact_replay':result,'canonical':9,'selected_inputs_and_extents':43,'frozen_author_and_prior_review_unchanged':True}))
if __name__=='__main__':main()
