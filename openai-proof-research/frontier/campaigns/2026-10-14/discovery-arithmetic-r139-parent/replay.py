#!/usr/bin/env python3
"""Read-only notified Arithmetic139 intake. Authentication is not a mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r139'
sp=importlib.util.spec_from_file_location('snap_helper',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_text())
def main():
    anchors={'FINAL.md':'b0fcb66279f7d9940f2241273ac93b4fe8f192885580c90e77c0d9016f1dfc63','private/MANIFEST.json':'2405e688459805a4fa12bae984de34aae1549e9676a30c9bcf99103947c9f08c','REPORT.md':'7a19d82169804376b15ba29f71ded05985e2f5511d746d3cdd3e92bf0c098df4'}
    before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);assert all(sha(ROOT/p)==v for p,v in anchors.items())
    r=subprocess.run(['python','-I','-B',str(ROOT/'verify_packet.py'),'--root',str(ROOT),'--final-sha',anchors['FINAL.md'],'--manifest-sha',anchors['private/MANIFEST.json'],'--report-sha',anchors['REPORT.md']],cwd=P,text=True,capture_output=True,check=True);assert not r.stderr
    result=json.loads(r.stdout);assert result['artifact_verification']=='MATCH' and result['payload_files']==91
    tree=read(P/'sources/preprints-tree.json');lookup={x['path']:x for x in tree['tree']};assert not tree['truncated'] and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    canonical=read(ROOT/'private/source-identities.json');assert len(canonical)==16
    for x in canonical:
        p=P/x['local'];d=p.read_bytes();e=lookup[x['path']];assert p.resolve().is_relative_to(ROOT) and len(d)==x['size']==e['size'] and sha(p)==x['sha256'] and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['sha']==e['sha']
    stable={}
    for x in read(ROOT/'private/completed-exception-identities.json'):
        p=P/x['original'];assert sha(p)==x['sha256'] and p.read_bytes()==(ROOT/x['copy']).read_bytes();stable[x['original']]=sha(p)
    for x in read(ROOT/'private/original-sections.json'):
        p=P/x['path'];d=p.read_bytes();assert sha(p)==x['file_sha256'] and hashlib.sha256(d[x['start']:x['end']]).hexdigest()==x['selection_sha256'] and d[x['start']:x['end']]==(P/x['copy']).read_bytes();stable[x['path']]=sha(p)
    old=B/'fresh-structural-discovery-r17/original-scope.md';assert old.read_bytes()==(ROOT/'private/old-G4-scope.md').read_bytes();stable[old.relative_to(P).as_posix()]=sha(old)
    assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n')
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'author_validator':result,'artifact_only':True,'payload_files':91,'canonical_objects':16,'completed_originals':6,'original_sections':2,'old_full_G4_scope_matches':True,'stable_named_originals':stable,'entire_root_unchanged':True,'parent_semantic_reading':'Complete FINAL/REPORT/DERIVATIONS/PREFREEZE-INFINITE/UNRESOLVED/READING/selection-limits/verifier. DERIVATIONS read as [0,12500),[12500,24037). Source and primary semantic extents remain attributed to author; no inherited independent proof-reading claim.'}
    (O/'replay.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'payload_files':91,'canonical_objects':16,'originals':len(stable),'entire_root_unchanged':True,'artifact_only':True}))
if __name__=='__main__':main()
