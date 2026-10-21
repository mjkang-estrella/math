#!/usr/bin/env python3
"""Read-only explicit-anchor Ar140 intake; identity is not a mathematical grade."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r140'
sp=importlib.util.spec_from_file_location('snapshot',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_text())
def main():
    anchors={'FINAL.md':'631b828c2c9fed89eac5946cb340d6eb05cfa7f57e2f43d1300c24056efa5655','MANIFEST.json':'59f6faab250c78942e0bfb7de88bd11fec40522321b026aa8a0e43b3aa75f826','REPORT.md':'655dbe046f251c96a064de9d8b543d44c55e7751330fdb8d3498926ddcd3d9b9'}
    before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);assert all(sha(ROOT/p)==v for p,v in anchors.items())
    r=subprocess.run(['python','-I','-B',str(ROOT/'verify_packet.py'),'--root',str(ROOT),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']],cwd=P,text=True,capture_output=True,check=True);assert not r.stderr
    manifest=read(ROOT/'MANIFEST.json');assert len(manifest['entries'])==107
    names={x['path']for x in manifest['entries']};outside={'FINAL.md','MANIFEST.json','REPORT.md','ANCHORS.json','VERIFICATION.txt'};actual={p for p,x in before.items()if x['kind']=='file'};assert actual==names|outside,(actual-names-outside,names-actual)
    tree=read(P/'sources/preprints-tree.json');lookup={x['path']:x for x in tree['tree']};assert not tree['truncated'] and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    canonical=read(ROOT/'private/source-identities.json');assert len(canonical)==49
    for x in canonical:
        p=P/x['local'];d=p.read_bytes();e=lookup[x['path']];assert p.resolve().is_relative_to(ROOT) and len(d)==x['size']==e['size'] and sha(p)==x['sha256'] and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['sha']==e['sha']
    stable={}
    completed=['discovery-arithmetic-r139-parent/assessment.md','fresh-arithmetic-discovery-r139/FINAL.md','fresh-arithmetic-discovery-r139/DERIVATIONS.md','fresh-arithmetic-discovery-r139/UNRESOLVED.md','fresh-arithmetic-discovery-r139/private/READING.md','fresh-arithmetic-discovery-r139/private/selection-limits.md']
    for name in completed:
        copy=ROOT/('private/completed-'+name.replace('/','_'));p=B/name;assert copy.read_bytes()==p.read_bytes();stable[p.relative_to(P).as_posix()]=sha(p)
    sections=read(ROOT/'private/original-sections.json');assert len(sections)==7
    for x in sections:
        p=P/x['path'];assert p.stat().st_size==x['source_bytes'] and sha(p)==x['source_sha256']
        with p.open('rb')as f:f.seek(x['start']);d=f.read(x['end']-x['start'])
        assert hashlib.sha256(d).hexdigest()==x['section_sha256'] and d==(P/x['copy']).read_bytes();stable[x['path']]=sha(p)
    assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n')
    result={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'author_verifier_stdout':r.stdout.strip(),'parent_exact_file_membership_checked':True,'payload_files':107,'canonical_objects':49,'canonical_distinct_sha256':len({x['sha256']for x in canonical}),'completed_originals':6,'selected_original_sections':7,'stable_named_originals':stable,'entire_root_unchanged':True,'artifact_only':True,'parent_semantic_reading':'Complete DERIVATIONS/UNRESOLVED/FINAL/REPORT/READING/selection-limits/verifier. Actual canonical and primary semantic extents remain attributed to author; parent did not reread all operative proof bodies.'}
    (O/'replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'payload_files':107,'canonical_objects':49,'selected_original_sections':7,'completed_originals':6,'entire_root_unchanged':True,'artifact_only':True}))
if __name__=='__main__':main()
