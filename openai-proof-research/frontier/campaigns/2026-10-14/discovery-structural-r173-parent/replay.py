#!/usr/bin/env python3
"""Read-only Structural173 selected-packet authentication, without mathematical grades."""
import hashlib, importlib.util, json, stat, subprocess, sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];R=B/'fresh-structural-discovery-r173'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r161-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'private/packet/FINAL.json':'b7f43c8c964b151f8e2fec6bf5e001b54a19007536c7e2d51b9b6116ca638e15','private/packet/MANIFEST.json':'bbb5b32c2b5015299117d86b810c4ab1efdbe75d80d99432c4c37267733a7bfa','REPORT.md':'4eec11af8693a17ab923966ee2f108e3dbe9ca8f897ab74201dfc820beef535f'}
def read(f):return json.loads(f.read_text())
def dump(n,v):(O/n).write_text(json.dumps(v,indent=2)+'\n')
def main():
    before=snap(R);mode=stat.S_IMODE(R.stat().st_mode);status=read(O/'task-status.json')['structuredContent'];assert status['status']=='completed' and status['workState']=='result_available' and not status['hasPendingChildRuns'] and not status['hasPendingQuestion'] and status['pendingApproval'] is None
    assert all(sha(R/n)==v and v in status['summary']for n,v in ANCHORS.items());m=read(R/'private/packet/MANIFEST.json');assert len(m['files'])==88 and {n for n,e in before.items()if e['kind']=='file'}==set(m['files'])|set(ANCHORS)
    tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(R/'private/source-objects.json');assert len(source)==16
    for e in source:
        f=R/e['local'];raw=f.read_bytes();node=entries[e['path']];assert len(raw)==e['size']==node['size'] and sha(f)==e['sha256'] and hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==e['git_blob']==node['sha'] and e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
    records=[]
    for n in ['acquisitions.json','acquisitions-2.json','Losert1987-identity.json','Dekimpe2000-acquisition-2.json','Tessera2008-acquisition.json']:
        x=read(R/'private/primary'/n);records.extend(x if isinstance(x,list)else[x])
    assert len(records)==9
    for e in records:
        digest=e.get('pdf_sha256',e.get('sha256'));size=e.get('pdf_size',e.get('size'));matches=[R/n for n,v in m['files'].items()if v['sha256']==digest];assert len(matches)==1 and matches[0].stat().st_size==size and matches[0].read_bytes().startswith(b'%PDF');texts=[R/n for n,v in m['files'].items()if v['sha256']==e['text_sha256']];assert texts and texts[0].stat().st_size==e['text_size']
    stable={};history=read(R/'private/history-reads.json');direct=read(R/'private/direct-reads.json');assert len(history)==2 and len(direct)==12
    for e in history+direct:
        if 'range'not in e:
            f=P/e['original'];assert sha(f)==e['original_sha256'];stable[e['original']]={'path':e['original'],'sha256':e['original_sha256']};continue
        f=P/e['original'];a,b=e['range'];raw=f.read_bytes();assert (R/e['local']).read_bytes()==raw[a:b] and sha(R/e['local'])==e['selected_sha256'] and oct(stat.S_IMODE(f.stat().st_mode))==e['mode']
        if a==0 and b==e['original_size']:assert len(raw)==e['original_size'] and sha(f)==e['original_sha256'];stable[e['original']]={'path':e['original'],'sha256':e['original_sha256']}
        elif e in history:assert len(raw)==e['original_size'] and sha(f)==e['original_sha256'];stable[e['original']]={'path':e['original'],'sha256':e['original_sha256']}
    result=subprocess.run([sys.executable,'-I','-B',str(R/'private/verify_packet.py'),str(R),'--final',ANCHORS['private/packet/FINAL.json'],'--manifest',ANCHORS['private/packet/MANIFEST.json'],'--report',ANCHORS['REPORT.md']],cwd=P,capture_output=True,text=True,timeout=30);assert result.returncode==0,(result.stdout,result.stderr)
    controls=read(R/'private/copied-control-observations.json');assert controls['baseline']['files']==controls['restored']['files']==2 and len(controls['controls'])==3 and all(e['observed']=='rejected'for e in controls['controls'])
    assert snap(R)==before and stat.S_IMODE(R.stat().st_mode)==mode and all(sha(P/e['path'])==e['sha256']for e in stable.values())
    dump('observed-root.json',{'root':before,'root_mode':mode});dump('replay.json',{'anchors':ANCHORS,'payload_files':88,'whole_root_files':91,'source_objects':16,'source_bytes':sum(e['size']for e in source),'primary_PDF_text_pairs':9,'direct_original_selections':12,'history_sections':2,'stable_named_originals':list(stable.values()),'read_only_verifier':{'returncode':result.returncode,'stdout':result.stdout.strip()},'recorded_reduced_copied_controls_checked':True,'root_unchanged':True,'limits':'Artifact authentication only. Parent read complete report/start/calculation/outcome/reading record/verifier; calculation split at byte14000. Protected source/primary/history proof bodies authenticated, not semantically reread by parent. Late source ancestry, incomplete transitive reading and late direct baselines remain disclosed. Nested private seals/metadata remain local. Source108 metadata initially sought build/main; actual build/source/main recovered within same selected family, no second screen.'});print(json.dumps({'payload':88,'files':91,'source_objects':16,'primary_pairs':9,'stable_originals':len(stable),'root_unchanged':True,'mathematical_gate':False}))
if __name__=='__main__':main()
