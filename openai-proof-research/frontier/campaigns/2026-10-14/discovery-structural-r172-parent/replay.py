#!/usr/bin/env python3
"""Read-only Structural172 handoff authentication, without mathematical grades."""
import hashlib, importlib.util, json, stat, subprocess, sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];R=B/'fresh-structural-discovery-r172'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r161-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'private/packet/FINAL.json':'ebe3fb44613b18993a9f0cfb39fa5de2cdc6aff7625a603107fc4e175e78db5f','private/packet/MANIFEST.json':'c0d9113ec4e59e05e4f262e6d73de0e7b7a4637d8e0ed8d37b3ee5b0bf509857','REPORT.md':'cb7c0f32eedcc5dae0025f8fdaabf7e7635fd756cc437207cd1670c20f8bbaad'}
def read(f):return json.loads(f.read_text())
def dump(n,v):(O/n).write_text(json.dumps(v,indent=2)+'\n')
def main():
    before=snap(R);mode=stat.S_IMODE(R.stat().st_mode);status=read(O/'task-status.json')['structuredContent']
    assert status['status']=='completed' and status['workState']=='result_available' and not status['hasPendingChildRuns'] and not status['hasPendingQuestion'] and status['pendingApproval'] is None
    assert all(sha(R/n)==v and v in status['summary']for n,v in ANCHORS.items())
    manifest=read(R/'private/packet/MANIFEST.json');assert len(manifest['inventory']['files'])==84
    assert {n for n,e in before.items()if e['kind']=='file'}==set(manifest['inventory']['files'])|set(ANCHORS)
    tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    source=read(R/'private/source-objects.json');assert len(source)==11 and sum(e['size']for e in source)==238520
    for e in source:
        f=R/e['local'];raw=f.read_bytes();node=entries[e['path']];assert len(raw)==e['size']==node['size'] and sha(f)==e['sha256'] and hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==e['sha']==node['sha'] and e['raw_url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
    records=[]
    for n in ['acquisitions.json','later-acquisitions.json','cornulier-acquisition.json','ma-acquisition.json','ma-fiber-acquisition.json']:
        x=read(R/'private/primary'/n);records.extend(x if isinstance(x,list)else[x])
    primary=[e for e in records if'sha256'in e];assert len(primary)==11
    pdfs={sha(R/n):R/n for n in manifest['inventory']['files']if n.startswith('private/primary/')and n.endswith('.pdf')};assert len(pdfs)==11
    for e in primary:
        f=pdfs[e['sha256']];assert f.stat().st_size==e['bytes'] and f.read_bytes().startswith(b'%PDF') and f.with_suffix('.txt').is_file()
    stable=[];history=read(R/'private/history-reads.json');assert len(history)==5
    for e in history:
        f=P/e['path'];raw=f.read_bytes();a,b=e['extent'];assert sha(f)==e['sha256'] and oct(stat.S_IMODE(f.stat().st_mode))==e['mode'] and raw[a:b]==(R/e['copy']).read_bytes();stable.append({'path':e['path'],'sha256':e['sha256']})
    direct=read(R/'private/direct-anchor-records.json');assert len(direct['completed_exceptions'])==6
    for e in direct['direct']+direct['completed_exceptions']:
        f=P/e['path'];raw=f.read_bytes()
        if 'selected_bytes_half_open'in e:
            a,b=e['selected_bytes_half_open'];assert hashlib.sha256(raw[a:b]).hexdigest()==e['selected_sha256']
        else:assert len(raw)==e['bytes'] and sha(f)==e['sha256'] and oct(stat.S_IMODE(f.stat().st_mode))==e['mode'];stable.append({'path':e['path'],'sha256':e['sha256']})
    result=subprocess.run([sys.executable,'-I','-B',str(R/'private/verify_packet.py'),str(R),'--final',ANCHORS['private/packet/FINAL.json'],'--manifest',ANCHORS['private/packet/MANIFEST.json'],'--report',ANCHORS['REPORT.md']],cwd=P,capture_output=True,text=True,timeout=30);assert result.returncode==0,(result.stdout,result.stderr)
    controls=read(R/'private/controls/observations.json');assert controls['reduced_packet_anchors']['payload_files']==2 and controls['unmodified_copy']['exit']==0 and controls['changed_payload_copy']['exit']==controls['wrong_detached_anchor']['exit']==1
    assert snap(R)==before and stat.S_IMODE(R.stat().st_mode)==mode and all(sha(P/e['path'])==e['sha256']for e in stable)
    dump('observed-root.json',{'root':before,'root_mode':mode});dump('replay.json',{'anchors':ANCHORS,'payload_files':84,'whole_root_files':87,'source_objects':11,'source_bytes':238520,'primary_PDF_text_pairs':11,'primary_semantic_body_pairs_reported':10,'stable_named_originals':stable,'completed_history_originals':5,'completed_direct_exceptions':6,'read_only_verifier':{'returncode':result.returncode,'stdout':result.stdout.strip()},'recorded_reduced_controls_checked':True,'root_unchanged':True,'limits':'Artifact checks only. Parent read full REPORT/start/calculation/outcome/verifier/reading account, with combined display truncation recovered from calculations byte14000 to end and full outcome separately. Parent did not semantically reread protected source, primary or historical proof bodies. Initially expected top-level FINAL.md; REPORT revealed nested private/packet envelopes, read without moving them. Original records preserve late r171 baselines, failed versions, partial primary coverage and false admissions. Private identities/replay remain local.'})
    print(json.dumps({'payload':84,'files':87,'source_objects':11,'primary_pairs':11,'stable_originals':len(stable),'root_unchanged':True,'mathematical_gate':False}))
if __name__=='__main__':main()
