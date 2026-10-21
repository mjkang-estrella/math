#!/usr/bin/env python3
"""Completed structural149 artifact archive and bounded disposable-copy replay."""
import datetime,hashlib,importlib.util,json,shutil,stat,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r149'
spec=importlib.util.spec_from_file_location('archive_helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha=h.sha
def snap(root):
    d=h.snap(root);d['.']={'kind':'directory','mode':stat.S_IMODE(root.lstat().st_mode)};return d
ANCHORS={'FINAL.md':'9c1f5c91ad3b3474172bcbe45afe5b3a4b9cad28fc0daab7f405805f6f87c742','MANIFEST.json':'e4221f8fc905d88e7fa44078e166a86c2f6be8aa879732d7c665c670fcafedb4','REPORT.md':'cb2f48e415ee9ce2145b5f236cd623a3d3b0d2c4224c7d0f3b0bf8c17cea625b'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
    now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P)
    assert len(read(B/'tasks.json')['tasks'])==504
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'initial_index_empty':True,'task_count':504,'task_index':501,'protected_unrelated_sha256':PROTECTED})
    before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current whole completed root including root-directory mode; no historical whole-project or OS certificate.'})
    st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and not st['hasPendingChildRuns'] and all(v in st['summary'] for v in ANCHORS.values())
    assert all(sha(ROOT/n)==v for n,v in ANCHORS.items())
    m=read(ROOT/'MANIFEST.json');assert m['schema']=='r149-exact-tree-v1' and len(m['files'])==103 and len(m['directories'])==23
    assert {p for p,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS)
    assert {p for p,e in before.items() if e['kind']=='directory'}==set(m['directories'])
    assert all(e['kind'] in ['file','directory'] and (e['kind']!='file' or e['nlink']==1) for e in before.values())
    for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['bytes'] and sha(ROOT/n)==e['sha256']
    tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    source=read(ROOT/'private/source-receipts.json')+read(ROOT/'private/source169-receipts.json');assert len(source)==46
    for e in source:
        data=(ROOT/e['local']).read_bytes();node=entries[e['path']]
        assert e['local']=='private/source/'+e['path'] and len(data)==e['bytes']==node['size'] and sha(ROOT/e['local'])==e['sha256']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha']
        assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
    incoming=read(ROOT/'private/incoming-authentication.json');assert incoming['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb' and incoming['tree_sha256']==sha(tp)
    assert [e['path'] for e in incoming['pinned_source_files']]==[e['path'] for e in source]
    for e in incoming['pinned_source_files']:assert sha(ROOT/e['local'])==e['sha256'] and e['authenticated']
    stable=[];mutable=[];assert len(incoming['late_local_original_snapshots'])==19
    for e in incoming['late_local_original_snapshots']:
        p=P/e['path'];assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256']
        if e['path']=='frontier/NEW-TEN-2026-10-14.md':mutable.append(e|{'limit':'Matched at this observation only; mutable journal is not a later stability input.'})
        else:stable.append(e|{'limit':'Late named current original hash, not retained-copy/first-read/history certificate or fresh semantic reading.'})
    assert len(stable)==18 and len(mutable)==1
    primary=[]
    for n in ['receipts.json','receipts2.json','receipts3.json','receipts4.json','receipts5.json']:
        d=read(ROOT/'private/primary'/n);primary+=d if isinstance(d,list) else [d]
    good=bad=0
    for e in primary:
        assert e['url'].startswith('https://arxiv.org/pdf/')
        if 'error' in e:assert e['name'] in ['harvey-olver-v2','hikita-v3'] and '404' in e['error'];bad+=1;continue
        p=ROOT/'private/primary'/(e['name']+'.pdf');assert p.stat().st_size==e.get('pdf_bytes',e.get('bytes')) and sha(p)==e.get('pdf_sha256',e.get('sha256')) and sha(p.with_suffix('.txt'))==e['text_sha256'];good+=1
    assert (good,bad)==(7,2)
    ctl=read(ROOT/'private/control-results.json');fixture=ROOT/'private/reduced-control';assert len(ctl['reduced_copy_membership'])==4 and len(ctl['results'])==6
    for n,v in ctl['fresh_reduced_copy_anchors'].items():assert sha(fixture/n)==v
    fm=read(fixture/'MANIFEST.json');assert set(fm['files'])==set(ctl['reduced_copy_membership'])
    pairs={'calculation.md':'notes/01-prefreeze-calculations.md','diagnostic.py':'code/graded_boundary.py','source-section.tex':'private/source/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/build/sections/02-graphs.tex','verify.py':'code/verify.py'}
    changed=[]
    for copy,original in pairs.items():
        assert sha(fixture/copy)==ctl['selected_original_hashes_before_and_after'][original]==fm['files'][copy]['sha256']
        if sha(ROOT/original)!=sha(fixture/copy):changed.append(original)
    assert changed==['notes/01-prefreeze-calculations.md']
    assert all((e['exit_code']==0)==e['expected_accept'] for e in ctl['results'].values())
    cases=[];diagnostics=[]
    with tempfile.TemporaryDirectory(prefix='structural149-copy-',dir=O) as temp:
        copy=Path(temp)/'packet';shutil.copytree(ROOT,copy)
        args=['--root',str(copy),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']]
        def check(label,want,custom=None):
            state=snap(copy);r=subprocess.run([sys.executable,'-B',str(copy/'code/verify.py'),*(custom or args)],text=True,capture_output=True,timeout=30)
            assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state
            cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
        check('baseline_full_packet',True)
        p=copy/'notes/02-integrated-reduction-and-gap.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('modified_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data)
        p=copy/'private/.extra';p.write_text('extra');check('extra_hidden_file',False);p.unlink()
        p=copy/'private/.empty';p.mkdir();check('extra_empty_directory',False);p.rmdir()
        wrong=args.copy();wrong[5]='0'*64;check('wrong_external_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
        for script,out in [('graded_boundary.py','graded-boundary-diagnostics.json'),('variable_boundary.py','variable-boundary-diagnostics.json'),('closed_weight_probe.py','closed-weight-diagnostics.json')]:
            state=snap(copy);r=subprocess.run([sys.executable,'-B',str(copy/'code'/script)],text=True,capture_output=True,check=True,timeout=45)
            assert snap(copy)==state and (copy/'notes'/out).read_bytes()==(ROOT/'notes'/out).read_bytes()
            diagnostics.append({'script':script,'stdout':json.loads(r.stdout),'complete_copied_root_bytes_and_modes_unchanged':True,'limit':'Writer reran on disposable copy and regenerated identical bytes; no claim it performed no writes.'})
    a=read(ROOT/'notes/graded-boundary-diagnostics.json');b=read(ROOT/'notes/variable-boundary-diagnostics.json');c=read(ROOT/'notes/closed-weight-diagnostics.json')
    assert len(a)==126 and len(b)==240 and all(e['equal'] and e['color']==e['tableau'] for e in a+b) and c['closed_walks']==368
    assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in PROTECTED.items())
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':5,'copy_removed':True,'whole_actual_root_unchanged':True,'historical_reduced_copy_note01_is_earlier_revision':True,'limits':'Full-copy integrity controls only; old six reduced-copy tests and own-note revision chronology remain separate.'})
    dump('diagnostic-replay.json',{'runs':diagnostics,'constant_width_comparisons':126,'varying_width_comparisons':240,'closed_walk_probes':368,'limits':'Bounded exact comparisons on disposable copy; no all-boundary trace identification, coefficientwise positivity or math/contribution grade.'})
    dump('input-authentication.json',{'source_blobs':46,'primary_pdf_text_pairs':7,'failed_primary_versions':2,'named_current_originals':19,'stable_originals':18,'mutable_journal':1,'retained_original_copy_count':0,'limits':'Late original identities and canonical source metadata; no external whole-original copies, fresh network/source/primary semantic or PDF visual read.'})
    dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':103,'whole_root_files':106,'directories_including_root':23,'source_blobs':46,'primary_pdf_text_pairs':7,'stable_named_originals':stable,'mutable_journal_observations':mutable,'artifact_cases':7,'negative_cases':5,'trace_comparisons':366,'closed_walk_probes':368,'whole_actual_root_unchanged':True,'limits':'Integrity and bounded diagnostics only; no universal proof, independent mathematical/contribution grade or fresh protected-body semantic reading. Verifier binds exact directory membership,not modes; parent snapshots include root mode.'})
    print(json.dumps({'files':106,'directories_including_root':23,'sources':46,'primary_pairs':7,'stable_originals':18,'cases':7,'trace_comparisons':366,'closed_walks':368}))
if __name__=='__main__':main()
