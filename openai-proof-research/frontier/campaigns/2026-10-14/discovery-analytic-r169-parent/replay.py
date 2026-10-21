#!/usr/bin/env python3
"""Explicit-anchor read-only Analytic169 archive; byte checks are not math gates."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-analytic-discovery-r169'
sp=importlib.util.spec_from_file_location('snapshot',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_text())
def main():
    anchors={'FINAL.md':'17ecbfcff0fa12c043b3a166f9987af17e8c553df26af5b97d3213557b0af42b','MANIFEST.json':'eaf9fc08df55a7d4fa36236bba325723d30b0680c5b50dc94ecb55518859efac','REPORT.md':'dee1d0681046026709e117e393f0be4998029988770c0ebdeac9fa84c99034ec'}
    before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);assert all(sha(ROOT/p)==v for p,v in anchors.items())
    r=subprocess.run(['python','-I','-B',str(ROOT/'VERIFY.py'),'--root',str(ROOT),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']],cwd=P,text=True,capture_output=True,check=True);assert not r.stderr;result=json.loads(r.stdout);assert result['artifact_check']=='pass' and result['selected_files']==67 and result['canonical_blobs']==28
    tree=read(P/'sources/preprints-tree.json');lookup={x['path']:x for x in tree['tree']};assert not tree['truncated'] and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    canonical=read(ROOT/'private/canonical-bindings.json');assert len(canonical)==28
    for x in canonical:
        p=ROOT/x['local'];d=p.read_bytes();e=lookup[x['path']];assert p.resolve().is_relative_to(ROOT) and len(d)==x['size']==e['size'] and sha(p)==x['sha256'] and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['sha']==e['sha']
    stable={};direct=read(ROOT/'private/direct-read-bindings.json')
    for x in direct:
        p=P/x['path']
        with p.open('rb')as f:f.seek(x['start']);d=f.read(x['end']-x['start'])
        assert hashlib.sha256(d).hexdigest()==x['sha256']
        if x['start']==0 and x['end']==p.stat().st_size:stable[x['path']]=sha(p)
    sections=read(ROOT/'private/original-extents.json');assert len(sections)==3
    for i,x in enumerate(sections):
        p=P/x['path'];assert sha(p)==x['whole_sha256']
        with p.open('rb')as f:f.seek(x['start']);d=f.read(x['end']-x['start'])
        assert hashlib.sha256(d).hexdigest()==x['section_sha256'] and d==(ROOT/f'private/original-section-{i}.txt').read_bytes();stable[x['path']]=sha(p)
    assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n')
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'author_validator':result,'artifact_only':True,'payload_files':67,'canonical_objects':28,'direct_ranges':direct,'original_sections':3,'stable_named_originals':stable,'entire_root_unchanged':True,'parent_semantic_reading':'Complete SESSION/FINAL/REPORT/CALCULATIONS/OBSTRUCTION/COMPARISON/READING-LIMITS/VERIFY. Minor aggregate truncation in OBSTRUCTION recovered by full separate read. Source and primary semantic extents remain attributed to author.'}
    (O/'replay.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'payload_files':67,'canonical_objects':28,'direct_ranges':len(direct),'original_sections':3,'entire_root_unchanged':True,'artifact_only':True}))
if __name__=='__main__':main()
