#!/usr/bin/env python3
"""Read-only Arithmetic144 detached-anchor intake; no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r144'
sp=importlib.util.spec_from_file_location('snapshot',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def main():
    anchors={'FINAL.md':'68f17106176b3bef5eba099bf4d446b82ed318c91a04bace4d019fc7693ba02d','MANIFEST.json':'cfc36b27c7ab95d89f325f3d1ead70c781323e7b04408262603eda3367bfa418','REPORT.md':'227b1dc13178cc1d32d9e719d04df5bb92f7663e438d49fceff6ffed6631aa63'}
    before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);assert all(sha(ROOT/p)==v for p,v in anchors.items())
    r=subprocess.run(['python','-I','-B',str(ROOT/'verify.py'),'--root',str(ROOT),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']],cwd=P,text=True,capture_output=True,check=True);assert not r.stderr and '78 payload files' in r.stdout
    m=read(ROOT/'MANIFEST.json');assert len(m['files'])==78;names={x['path']for x in m['files']};assert {p for p,x in before.items()if x['kind']=='file'}==names|{'MANIFEST.json','REPORT.md','ANCHORS.json'}
    tree=read(P/'sources/preprints-tree.json');lookup={x['path']:x for x in tree['tree']};assert not tree['truncated']and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    canonical=read(ROOT/'private/source-bindings.json');assert len(canonical)==11
    for x in canonical:
        p=P/x['local'];data=p.read_bytes();e=lookup[x['path']];assert p.resolve().is_relative_to(ROOT)and len(data)==x['size']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==x['sha']==e['sha']
    stable={};direct=read(ROOT/'private/completed-direct-extents.json');assert len(direct)==6
    for x in direct:
        p=P/x['original'];assert x['start']==0 and x['end']==p.stat().st_size and sha(p)==x['sha256']and p.read_bytes()==(ROOT/x['copy']).read_bytes();stable[x['original']]=sha(p)
    sections=[]
    for x in read(ROOT/'private/history-extents.json'):
        p=P/x['path']
        with p.open('rb')as f:f.seek(x['start']);data=f.read(x['end']-x['start'])
        assert hashlib.sha256(data).hexdigest()==x['selected_sha256']and data==(ROOT/x['copy']).read_bytes();sections.append({'path':x['path'],'start':x['start'],'end':x['end'],'selection_sha256':x['selected_sha256'],'basis':'author selected-range hash; no fabricated whole-original acquisition digest'})
    assert len(sections)==5 and snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n');result={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'author_verifier_stdout':r.stdout.strip(),'parent_exact_file_membership_checked':True,'payload_files':78,'outside_envelopes':3,'canonical_objects':11,'completed_originals':6,'selected_original_sections':5,'stable_named_originals':stable,'history_section_anchors':sections,'history_checks_bind_selected_ranges_only':True,'entire_root_unchanged':True,'artifact_only':True,'parent_semantic_reading':'Complete DERIVATIONS/UNRESOLVED/FINAL/REPORT/private READING/selection-limits/verifier. Actual source/primary/history semantic extents remain attributed to author. Only bounded Source046 catalogue body read for next discovery.'};(O/'replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k]for k in ['payload_files','canonical_objects','completed_originals','selected_original_sections','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
