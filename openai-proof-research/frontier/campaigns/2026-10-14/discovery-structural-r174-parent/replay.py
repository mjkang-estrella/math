#!/usr/bin/env python3
"""Read-only completed Structural174 packet authentication, no mathematical gate."""
import hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-structural-discovery-r174'
sp=importlib.util.spec_from_file_location('identity',B/'discovery-analytic-r161-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_text())
def main():
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode);anchors={'private/packet/FINAL.json':'c7c39a42daaccc52c8d0b7537687639e7ea6badbb6365c760e186fb605151dca','private/packet/MANIFEST.json':'a382e7e618b89e34c388a8a53c4243f5cdd83cf62f3c5acafca9c14425af13e6','REPORT.md':'315a436eb7160306d8e42ed3857e363ccee40b14f87e960a85cdd8b95a62e7da'}
    result=json.loads(subprocess.check_output(['python','-I','-B',str(A/'private/verify-packet.py'),str(A),'--final-sha256',anchors['private/packet/FINAL.json'],'--manifest-sha256',anchors['private/packet/MANIFEST.json'],'--report-sha256',anchors['REPORT.md']],cwd=P,text=True));assert result['files']==80 and result['directories']==10
    tree=read(P/'sources/preprints-tree.json');assert len(tree['tree'])==13223 and not tree['truncated'] and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';entries={e['path']:e for e in tree['tree']};sources=read(A/'private/source-objects.json');assert len(sources)==13
    for e in sources:
        p=P/e['local'];data=p.read_bytes();assert len(data)==e['bytes']==entries[e['path']]['size'] and sha(p)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==entries[e['path']]['sha']
    primary=[]
    for name in ['acquisition.json','acquisition-cksv.json','acquisition-ems.json']:
        es=read(A/'private/primary'/name);primary+=es if isinstance(es,list)else[es]
    for e in primary:
        for ext,hash_key,size_key in [('pdf','sha256','bytes'),('txt','text_sha256','text_bytes')]:
            p=A/'private/primary'/(e['name']+'.'+ext);assert sha(p)==e[hash_key] and len(p.read_bytes())==e[size_key]
    stable={}
    checks=read(A/'private/input-preservation.json')['checks'];assert len(checks)==28
    for e in checks:
        if e['kind']=='canonical-source-local':continue
        p=P/e['path']
        if 'selected_sha256'in e:
            with p.open('rb')as f:f.seek(e['start']);data=f.read(e['end']-e['start'])
            assert hashlib.sha256(data).hexdigest()==e['selected_sha256']
        else:assert sha(p)==e['sha256'];stable[e['path']]=e['sha256']
    for e in read(A/'private/history-reads.json'):
        p=P/e['path'];data=p.read_bytes();assert sha(p)==e['original_sha256'] and len(data)==e['original_bytes'] and stat.S_IMODE(p.stat().st_mode)==e['original_mode'] and data[e['start']:e['end']]==(P/e['selected']).read_bytes() and sha(P/e['selected'])==e['sha256']
    assert snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n');(O/'replay.json').write_text(json.dumps({'anchors':anchors,'verifier':result,'canonical_objects':13,'primary_pdf_text_pairs':len(primary),'input_preservation_records':28,'stable_named_originals':stable,'selected_original_history_sections':3,'whole_root_unchanged':True,'mathematical_verdict':None},indent=2)+'\n');print(json.dumps({'artifact_replay':result,'canonical':13,'primary_pairs':len(primary),'original_records':28,'mathematical_gate':False}))
if __name__=='__main__':main()
