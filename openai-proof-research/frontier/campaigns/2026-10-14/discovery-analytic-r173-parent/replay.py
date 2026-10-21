#!/usr/bin/env python3
"""Read-only Analytic173 detached-anchor intake; no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-analytic-discovery-r173'
sp=importlib.util.spec_from_file_location('snapshot',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def main():
    anchors={'FINAL.md':'aca065e951ef8793769ed9c5bac556c3b6fe152b8a580415d5e19b76d97aaef5','MANIFEST.json':'e9b24857899530ff9551f6909a353c6a021ab7d3cf79f03cd5fc348504e204b0','REPORT.md':'4cdebd75e4099ae45b811d6dd3134626da0b73bfc062d1c56a9977d118fb2617'}
    before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);assert all(sha(ROOT/p)==v for p,v in anchors.items())
    r=subprocess.run(['python','-I','-B',str(ROOT/'verify_packet.py'),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']],cwd=P,text=True,capture_output=True,check=True);assert not r.stderr and r.stdout.startswith('ARTIFACT MATCH:')
    manifest=read(ROOT/'MANIFEST.json');assert len(manifest['files'])==83
    names={x['path']for x in manifest['files']};outside={'FINAL.md','MANIFEST.json','REPORT.md','ANCHORS.json'};assert {p for p,x in before.items()if x['kind']=='file'}==names|outside
    tree=read(P/'sources/preprints-tree.json');lookup={x['path']:x for x in tree['tree']};assert not tree['truncated']and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    canonical=read(ROOT/'private/source-authentication.json');assert len(canonical)==13
    for x in canonical:
        p=ROOT/'private/source'/Path(x['path']).name;data=p.read_bytes();e=lookup[x['path']];assert len(data)==x['bytes']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==x['git_blob']==e['sha']
    stable={};direct=read(ROOT/'private/completed-exceptions.json');assert len(direct)==7
    for x in direct:
        p=P/x['path'];assert x['bytes']==[0,p.stat().st_size]and sha(p)==x['sha256'];stable[x['path']]=x['sha256']
    sections=[]
    for x in read(ROOT/'private/original-extents.json'):
        p=P/x['path'];assert sha(p)==x['whole_sha256'];a,b=x['bytes']
        with p.open('rb')as f:f.seek(a);data=f.read(b-a)
        assert hashlib.sha256(data).hexdigest()==x['selected_sha256']and data==(ROOT/'private'/x['copy']).read_bytes();stable[x['path']]=x['whole_sha256'];sections.append({'path':x['path'],'start':a,'end':b,'selection_sha256':x['selected_sha256'],'timing':x.get('timing','author recorded whole/selected range hashes')})
    assert len(sections)==6
    for x in read(ROOT/'private/originals-unchanged.json'):assert x['unchanged']and sha(P/x['path'])==x['sha256']==stable[x['path']]
    assert len(stable)==12 and snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n')
    result={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'author_verifier_stdout':r.stdout.strip(),'parent_exact_file_membership_checked':True,'payload_files':83,'outside_envelopes':4,'canonical_objects':13,'completed_originals':7,'selected_original_sections':6,'stable_named_originals':stable,'history_section_anchors':sections,'retrospective_hash_registration_disclosed':True,'entire_root_unchanged':True,'artifact_only':True,'parent_semantic_reading':'Complete INTERFACES/CALCULATIONS/MIXED/BOUNDARY/COMPARISON/FINAL/REPORT/private READING-LIMITS/verifier. Actual source/primary/history semantic extents attributed to author; parent checked bindings and original range copies. Only bounded Source304 catalogue body read for next discovery.'}
    (O/'replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k]for k in ['payload_files','outside_envelopes','canonical_objects','completed_originals','selected_original_sections','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
