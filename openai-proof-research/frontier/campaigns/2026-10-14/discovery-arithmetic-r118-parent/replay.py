#!/usr/bin/env python3
"""Completed arithmetic118 byte archive; no mathematical execution or gate."""
import datetime,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r118'
spec=importlib.util.spec_from_file_location('archive_helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'b337fe4e203310e827525369d08d6ae81cc5b5993d8d89f4ba5797ee078a745a','MANIFEST.json':'dd13a49b68865fadbd7e88399b7bb809b468544d52d40b388500626ea8617c83','REPORT.md':'a1a5935f84f53efc5e2efafbab7ce1f7c4f08707512385e98cd97ffbb260bcdd'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
    now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P)
    assert len(read(B/'tasks.json')['tasks'])==515
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'initial_index_empty':True,'task_count':515,'task_index':513,'protected_unrelated_sha256':PROTECTED})
    before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current completed whole root excluding root-directory mode;no historical whole-project or OS certificate.'})
    st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and not st['hasPendingChildRuns'] and all(v in st['summary'] for v in ANCHORS.values())
    assert all(sha(ROOT/n)==v for n,v in ANCHORS.items())
    m=read(ROOT/'MANIFEST.json');assert m['schema']=='r118-exact-v1' and len(m['files'])==75 and len(m['directories'])==16
    assert {p for p,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS) and {p for p,e in before.items() if e['kind']=='directory'}==set(m['directories'])
    for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
    tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};packet=ROOT/'packet'
    source=read(packet/'source-identities.json');assert len(source)==22
    prefix='preprints/Milnes-rationality-conjecture-for-abelian-varieties-October-7-2026/';companion='preprints/The-rational-Hodge-conjecture-for-CM-abelian-varieties-October-6-2026/'
    assert {e['canonical_path'] for e in source}=={p for p,e in entries.items() if e['type']=='blob' and ((p.startswith(prefix) and p.endswith('.tex')) or (p.startswith(companion) and p.endswith(('.tex','.bib'))))}
    for e in source:
        data=(packet/e['path']).read_bytes();node=entries[e['canonical_path']]
        assert len(data)==e['size']==node['size'] and sha(packet/e['path'])==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha']
        assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
    primary=read(packet/'primary-identities.json');downloaded=[e for e in primary if 'path' in e];failures=[e for e in primary if 'failure' in e];assert len(downloaded)==len(failures)==2
    for e in downloaded:
        p=packet/e['path'];assert p.stat().st_size==e['size'] and sha(p)==e['sha256'] and sha(packet/e['extract_path'])==e['extract_sha256']
    stable=[];excerpts=[];incoming=read(packet/'incoming-identities.json');assert len(incoming['originals'])==14 and incoming['tree']['sha256']==sha(tp) and incoming['tree']['entries']==13223 and not incoming['tree']['truncated']
    for e in incoming['originals']:
        q=packet/e['copy_path'];assert q.stat().st_size==e['copy_size'] and sha(q)==e['copy_sha256']
        if e['whole_copy']:
            p=P/e['original_path'];assert p.read_bytes()==q.read_bytes() and p.stat().st_size==e['original_size'] and sha(p)==e['original_sha256'];stable.append({'path':e['original_path'],'sha256':e['original_sha256'],'bytes':e['original_size'],'limit':'Late current whole-copy equality,not first-read/inherited-archive certification or fresh semantic reading.'})
        else:excerpts.append(e|{'limit':'Retained excerpt only;old whole observation is not a current/future stability input.'})
    assert len(stable)==10 and len(excerpts)==4
    recheck=read(packet/'identity-recheck.json');assert recheck['canonical_sources']==22 and len(recheck['incoming'])==14 and all(e['copy_matches'] and e['whole_original_matches_capture'] for e in recheck['incoming']) and len(recheck['downloaded_primary_and_extracts_matched'])==2
    ctl=read(packet/'control-results.json');fixture=packet/'private/controls';fm=read(fixture/'MANIFEST.json')
    assert len(ctl['controls'])==7 and len(ctl['selection_mapping'])==3 and len(fm['files'])==3
    for n,v in ctl['anchors'].items():assert sha(fixture/n)==v
    for e in ctl['selection_mapping']:assert (packet/e['original']).read_bytes()==(fixture/e['copy']).read_bytes() and sha(packet/e['original'])==e['original_sha256']==e['copy_sha256']==fm['files'][e['copy']]['sha256']
    assert all(e['accepted']==e['expected_acceptance'] and e['read_only_snapshot_equal'] for e in ctl['controls'])
    cases=[]
    with tempfile.TemporaryDirectory(prefix='arithmetic118-copy-',dir=O) as temp:
        copy=Path(temp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),'--final',ANCHORS['FINAL.md'],'--manifest',ANCHORS['MANIFEST.json'],'--report',ANCHORS['REPORT.md']]
        def check(label,want,custom=None):
            state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'packet/code/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
            assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state
            cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
        check('baseline_full_packet',True)
        p=copy/'packet/notes/chow-specialization-reduction.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('modified_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data)
        p=copy/'packet/private/.extra';p.write_text('extra');check('extra_hidden_file',False);p.unlink();p=copy/'packet/private/.empty';p.mkdir();check('extra_empty_directory',False);p.rmdir()
        wrong=args.copy();wrong[4]='0'*64;check('wrong_external_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
    assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in PROTECTED.items())
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':5,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Seven complete disposable-copy controls;the child seven selected-copy tests remain separate.Artifact evidence only.'})
    dump('input-authentication.json',{'source_blobs':22,'primary_pdf_files':2,'byte_bound_extracts':2,'byte_bound_renders':6,'failed_primary_downloads':failures,'stable_whole_original_copies':10,'selected_excerpts':4,'selected_fixture_members':3,'limits':'Canonical local bytes/retained-copy binding only,no fresh network/protected-body semantic/visual reading;web excerpt payloads do not authenticate full remote PDFs or inherited archives.'})
    dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':75,'whole_root_files':78,'subdirectories':16,'source_blobs':22,'primary_pdf_files':2,'stable_named_originals':stable,'selected_original_excerpts':excerpts,'artifact_cases':7,'negative_cases':5,'whole_actual_root_unchanged':True,'limits':'Artifact archive only,no mathematical numerical/formal suite or independent grade.Verifier excludes modes,parent snapshots exclude rootmode.'})
    print(json.dumps({'files':78,'subdirectories':16,'source_blobs':22,'primary_pdfs':2,'stable_whole_originals':10,'excerpts':4,'cases':7}))

if __name__=='__main__':main()
