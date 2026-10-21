#!/usr/bin/env python3
"""Read-only Analytic165 archive authentication; no mathematical grade."""
import hashlib, importlib.util, json, stat, subprocess, sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];R=B/'fresh-analytic-discovery-r165'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r161-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'4bf5acddbd2c58cad7ef2ae20c4afa1eb9ccc18cd4c75717e81c24b850c3320d','private/MANIFEST.json':'376153517e64b2fc253b2157471d4c905d6ebde2827ada428b378b22afc5a05b','REPORT.md':'78b71d4111f68fc2290afd9ba678694902c44c06bf10694e503e7fd1bef4eea5'}
def read(f):return json.loads(f.read_text())
def dump(n,v):(O/n).write_text(json.dumps(v,indent=2)+'\n')
def main():
    before=snap(R);mode=stat.S_IMODE(R.stat().st_mode);status=read(O/'task-status.json')['structuredContent'];assert status['status']=='completed' and status['workState']=='result_available' and not status['hasPendingChildRuns'] and not status['hasPendingQuestion'] and status['pendingApproval'] is None
    assert all(sha(R/n)==v and v in status['summary']for n,v in ANCHORS.items());manifest=read(R/'private/MANIFEST.json');assert len(manifest['files'])==76
    excluded={'REPORT.md','private/MANIFEST.json','private/ANCHORS.json','private/CONTROL-RESULTS.json'}
    assert {e['path']for e in manifest['files']}=={n for n,e in before.items()if e['kind']=='file'and n not in excluded and not n.startswith('private/controls/')and '__pycache__'not in Path(n).parts}
    tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    source=read(R/'private/source-auth.json');assert len(source)==6
    for e in source:
        f=R/'private'/e['local'];raw=f.read_bytes();node=entries[e['path']];assert len(raw)==e['size']==node['size'] and sha(f)==e['sha256'] and hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==e['sha']==node['sha'] and e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
    accesses=[]
    for n in ['primary-access.json','primary-access-2.json','primary-access-3.json','primary-access-4.json','primary-access-5.json']:
        x=read(R/'private'/n);accesses.extend(x if isinstance(x,list)else[x])
    acquired=[e for e in accesses if'sha256'in e];assert len(acquired)==8
    for e in acquired:
        matches=[R/x['path']for x in manifest['files']if x['sha256']==e['sha256']];assert matches and matches[0].stat().st_size==e['bytes']
    originals=read(R/'private/originals.json');assert len(originals)==25;stable={}
    for e in originals:
        f=P/e['path'];raw=f.read_bytes();selected=raw[e['start']:e['end']];assert hashlib.sha256(selected).hexdigest()==e['selected_sha256'] and selected==(R/e['copy']).read_bytes() and stat.S_IMODE(f.stat().st_mode)==e['mode']
        if e['whole_sha256']:assert sha(f)==e['whole_sha256'];stable[e['path']]={'path':e['path'],'sha256':e['whole_sha256']}
    result=subprocess.run([sys.executable,'-I','-B',str(R/'private/verify.py'),'--root',str(R),'--final-sha',ANCHORS['FINAL.md'],'--manifest-sha',ANCHORS['private/MANIFEST.json'],'--report-sha',ANCHORS['REPORT.md'],'--project-root',str(P)],cwd=P,capture_output=True,text=True,timeout=30);assert result.returncode==0,(result.stdout,result.stderr)
    controls=read(R/'private/CONTROL-RESULTS.json')['results'];assert len(controls)==7 and all((e['returncode']==0)==e['expected_success']for e in controls)
    assert snap(R)==before and stat.S_IMODE(R.stat().st_mode)==mode and all(sha(P/e['path'])==e['sha256']for e in stable.values())
    dump('observed-root.json',{'root':before,'root_mode':mode});dump('replay.json',{'anchors':ANCHORS,'payload_members':76,'source_objects':6,'successful_primary_or_navigation_acquisitions':8,'original_selections':25,'stable_named_originals':list(stable.values()),'read_only_verifier':{'returncode':result.returncode,'stdout':result.stdout.strip()},'recorded_copied_mutation_deletion_restoration_controls_checked':True,'root_unchanged':True,'limits':'Artifact checks only. Parent read complete FINAL/REPORT/CALCULATIONS/REDUCTIONS, reading/isolation account and verifier. REDUCTIONS split at byte14000; no source/primary/history proof bodies semantically reread by parent. Manifest binds selected members, not arbitrary additions; parent independently matched selection after declared envelope/control/cache exclusions and snapshots the entire current root/modes. First expected top-level MANIFEST; REPORT specifies private/MANIFEST, read in place. Source366 catalogue uses a title-named PDF rather than paper.pdf; canonical prefix recovered from the same one selected family, no second screen. Protected inventories and replay remain local.'});print(json.dumps({'payload':76,'source_objects':6,'acquired_primary_or_navigation':8,'original_selections':25,'whole_stable_originals':len(stable),'root_unchanged':True,'mathematical_gate':False}))
if __name__=='__main__':main()
