#!/usr/bin/env python3
"""Read-only adoption of a full-scope INCOMPLETE contribution review."""
import hashlib, importlib.util, json, stat, subprocess, sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parents[1];P=B.parents[2];R=B/'arithmetic-r136-contribution-r1'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r161-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'d5102501a22c6e6282ac4bdf721a69a94e1c069d4cfb431b658412e770e0cf70','MANIFEST.json':'5771759568618bfde3d3576b3b42ff79622aaaa67c17f3de039735d4d94494ff','REPORT.md':'004399707b5d13abecb0ff7eb606a86c9ce69d444562f3ff87cbd87571bb5088'}
def read(f):return json.loads(f.read_text())
def dump(n,v):(O/n).write_text(json.dumps(v,indent=2)+'\n')
def main():
    before=snap(R);mode=stat.S_IMODE(R.stat().st_mode);status=read(O/'task-status.json')['structuredContent']
    assert status['status']=='completed' and status['workState']=='result_available' and not status['hasPendingChildRuns'] and not status['hasPendingQuestion'] and status['pendingApproval'] is None
    assert all(sha(R/n)==v and v in status['summary']for n,v in ANCHORS.items())
    m=read(R/'MANIFEST.json');assert m['verdict']=='INCOMPLETE' and len(m['payload'])==103
    assert m['frozen_sha256']=='cde199a706104ed0db542704b0470d451ce5e11bd7ff0cc74d62df68130b4a77' and m['author_proof_sha256']=='6c9ea784ead7d96835a69a3a41d15f89ec3a13ac4faa83b342a6adcc76c53446'
    assert {n for n,e in before.items()if e['kind']=='file'}=={e['path']for e in m['payload']}|set(ANCHORS)
    treep=P/'sources/preprints-tree.json';assert sha(treep)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(treep);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    source=read(R/'private/source-authentication.json');assert len(source)==9
    for e in source:
        members=[R/f['path']for f in m['payload']if f['sha256']==e['sha256']];assert members;raw=members[0].read_bytes();node=entries[e['path']];assert len(raw)==node['size'] and hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==e['blob']==node['sha']
    primary=read(R/'private/primary-independent-authentication.json');assert len(primary)==10
    pdfs={sha(R/e['path']):R/e['path']for e in m['payload']if e['path'].endswith('.pdf')}
    for e in primary:
        f=pdfs[e['sha256']];assert f.stat().st_size==e['bytes'] and f.read_bytes().startswith(b'%PDF') and e['matches_author']
    for e in read(R/'private/extraction-identities.json'):
        f=R/'private/primary-extract'/(e['name']+'.txt');assert f.stat().st_size==e['bytes'] and sha(f)==e['sha256'] and e['pdf_sha256']in pdfs
    stable={}
    for e in read(R/'private/copied-identities.json'):
        original=P/e['original'];copy=P/e['copy'];assert original.read_bytes()==copy.read_bytes() and original.stat().st_size==e['bytes'] and sha(original)==e['sha256'];stable[e['original']]={'path':e['original'],'sha256':e['sha256']}
    history=read(R/'private/history-reading.json');assert len(history)==2
    for e in history:
        f=P/e['path'];a,b=e['bytes'];owned=[R/x['path']for x in m['payload']if x['sha256']==e['selected_sha256']];assert len(owned)==1 and f.stat().st_size==e['total'] and sha(f)==e['sha256'] and oct(stat.S_IMODE(f.stat().st_mode))==e['mode'] and owned[0].read_bytes()==f.read_bytes()[a:b];stable[e['path']]={'path':e['path'],'sha256':e['sha256']}
    for e in read(R/'private/end-input-identities.json'):
        f=P/e['path'];assert f.stat().st_size==e['bytes'] and sha(f)==e['sha256'] and stat.S_IMODE(f.stat().st_mode)==e['mode']
    verifier=subprocess.run([sys.executable,'-I','-B',str(R/'verify_packet.py'),'--root',str(R),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']],cwd=P,capture_output=True,text=True,timeout=30);assert verifier.returncode==0,(verifier.stdout,verifier.stderr)
    finite=subprocess.run([sys.executable,'-I','-B',str(R/'private/verify-mathematics.py')],cwd=P,capture_output=True,text=True,timeout=30);assert finite.returncode==0,(finite.stdout,finite.stderr);certificate=json.loads(finite.stdout);assert certificate['passed'] and certificate['a']==469 and certificate['B']==20 and certificate['small_vector_norm']==10
    controls=read(R/'private/control-results.json')['results'];assert len(controls)==6 and controls[0]['accepted'] and all(x['rejected']for x in controls[1:])
    assert snap(R)==before and stat.S_IMODE(R.stat().st_mode)==mode and all(sha(P/e['path'])==e['sha256']for e in stable.values())
    dump('observed-root.json',{'root':before,'root_mode':mode});dump('finite-certificate.json',certificate);dump('replay.json',{'anchors':ANCHORS,'payload_files':103,'whole_root_files':106,'source_objects':9,'primary_PDF_text_pairs':10,'stable_named_originals':list(stable.values()),'history_originals':2,'read_only_verifier':{'returncode':verifier.returncode,'stdout':verifier.stdout.strip()},'finite_certificate_read_only':{'returncode':finite.returncode,'passed':True,'scope':'Finite arithmetic and discriminant-form identities; not the unknown-threshold frozen theorem'},'recorded_six_copied_controls_checked':True,'root_unchanged':True,'limits':'Parent read full review, FINAL/REPORT, reading record, verifier and finite-check code. Initial combined output truncated; full review recovered in two byte chunks, reading record separately. Protected source/primary/history bodies authenticated, not semantically reread by parent. Artifact verification is not a correctness or contribution grade.'});print(json.dumps({'payload':103,'files':106,'source_objects':9,'primary_pairs':10,'stable_originals':len(stable),'finite_certificate_passed':True,'root_unchanged':True}))
if __name__=='__main__':main()
