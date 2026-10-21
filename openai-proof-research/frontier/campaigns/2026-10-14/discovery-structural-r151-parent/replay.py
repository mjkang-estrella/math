#!/usr/bin/env python3
"""Completed structural151 artifact/finite archive,no universal mathematical gate."""
import datetime,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r151'
spec=importlib.util.spec_from_file_location('archive_helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'8b1cdb773fb38e45820625e40a75f67ff7da8bd12d56a6c719faa45ec8367f0f','MANIFEST.json':'d664dc6c9b051da8538bc7cd58db50b4599ba0771964c122395fdf5ada2e25df','REPORT.md':'da5629ffc31972962f88c7eb44ad64a17b5fced4e95fa996d0ed8fc19e841c9c'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
    now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P)
    assert len(read(B/'tasks.json')['tasks'])==511
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'initial_index_empty':True,'task_count':511,'task_index':507,'protected_unrelated_sha256':PROTECTED})
    before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current completed whole-root snapshot excluding root-directory mode;manifest separately names dot root,no historical whole-project or OS certificate.'})
    st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and not st['hasPendingChildRuns'] and all(v in st['summary'] for v in ANCHORS.values())
    assert all(sha(ROOT/n)==v for n,v in ANCHORS.items())
    m=read(ROOT/'MANIFEST.json');assert m['schema']=='r151-exact-payload-v1' and len(m['files'])==40 and m['envelopes_excluded']==list(ANCHORS)
    assert {p for p,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS)
    assert {p for p,e in before.items() if e['kind']=='directory'}|{'.'}==set(m['directories']) and len(m['directories'])==14
    for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
    tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    source=read(ROOT/'private/source-authentication.json');assert len(source)==10
    prefix='preprints/One-Sample-Suffices-for-Matroid-Prophet-Inequalities-against-an-Almighty-Adversary-September-23-2026/'
    assert {e['canonical_path'] for e in source}=={p for p,e in entries.items() if p.startswith(prefix) and e['type']=='blob' and not p.endswith('.pdf')}
    for e in source:
        data=(ROOT/e['local']).read_bytes();node=entries[e['canonical_path']]
        assert e['local']=='private/source/'+e['canonical_path'][len(prefix):] and len(data)==e['size']==node['size'] and sha(ROOT/e['local'])==e['sha256']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob_sha1']==node['sha']
        assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
    primary=read(ROOT/'private/primary/receipts.json');assert len(primary)==3
    for e in primary:
        p=ROOT/'private/primary'/(e['name']+'.pdf');assert p.stat().st_size==e['pdf_size'] and sha(p)==e['pdf_sha256'] and sha(p.with_suffix('.txt'))==e['text_sha256']
    originals=read(ROOT/'private/incoming-originals.json');assert len(originals)==15;stable=[];mutable=[]
    for e in originals:
        if e['mutable']:mutable.append(e|{'parent_current_sha256_observed':sha(P/e['path']),'limit':'Old mutable journal identity,not a current/future stability input;no body copy.'})
        else:assert (P/e['path']).stat().st_size==e['size'] and sha(P/e['path'])==e['sha256'];stable.append(e)
    assert len(stable)==14 and len(mutable)==1
    ctl=read(ROOT/'private/controls/results.json');fixture=ROOT/'private/controls/selected-copy';fm=read(fixture/'MANIFEST.json')
    assert len(ctl['results'])==8 and len(ctl['selected_originals'])==2 and set(fm['files'])=={e['source_relative'] for e in ctl['selected_originals']}
    for n,v in ctl['selected_copy_anchors'].items():assert sha(fixture/n)==v
    for e in ctl['selected_originals']:
        n=e['source_relative'];assert (fixture/n).read_bytes()==(ROOT/n).read_bytes() and sha(ROOT/n)==e['sha256']==fm['files'][n]['sha256'] and (fixture/n).stat().st_size==e['size']
    assert all((e['returncode']==0)==e['expected_accept'] and e['before']==e['after'] for e in ctl['results'])
    cases=[]
    with tempfile.TemporaryDirectory(prefix='structural151-copy-',dir=O) as temp:
        copy=Path(temp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),'--final',ANCHORS['FINAL.md'],'--manifest',ANCHORS['MANIFEST.json'],'--report',ANCHORS['REPORT.md']]
        def check(label,want,custom=None):
            state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'code/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
            assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state
            cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
        check('baseline_full_packet',True)
        p=copy/'notes/02-integrated-reduction-and-gap.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('modified_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data)
        p=copy/'private/.extra';p.write_text('extra');check('extra_hidden_file',False);p.unlink();p=copy/'private/.empty';p.mkdir();check('extra_empty_directory',False);p.rmdir()
        wrong=args.copy();wrong[4]='0'*64;check('wrong_external_manifest_anchor',False,wrong)
        p=copy/'REPORT.md';data=p.read_bytes();p.write_bytes(data+b'CONTROL\n');check('changed_outside_REPORT',False);p.write_bytes(data);check('restored',True)
        state=snap(copy);d=subprocess.run([sys.executable,'-I','-B',str(copy/'code/payoff_diagnostic.py')],capture_output=True,text=True,timeout=60)
        assert d.returncode==0,(d.stdout,d.stderr);result=json.loads(d.stdout);assert result==read(ROOT/'notes/finite-diagnostic.json') and snap(copy)==state==before
        dump('diagnostic-replay.json',{'program_sha256':sha(ROOT/'code/payoff_diagnostic.py'),'result':result,'stderr':d.stderr,'disposable_full_copy_unchanged':True,'limits':'Existing bounded stdout-only finite diagnostic replay,no arbitrary-matroid or unconditional performance guarantee and no independent gate.'})
    assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in PROTECTED.items())
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':6,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Eight complete disposable-copy controls;child eight selected-copy controls remain separate.Artifact evidence only.'})
    dump('input-authentication.json',{'source_blobs':10,'primary_pdf_text_pairs':3,'byte_bound_render':1,'stable_originals':14,'mutable_journal':1,'retained_original_copies':0,'selected_fixture_members':2,'limits':'Local canonical source/blob and byte identities only,no fresh protected-body semantic/remote identity/visual reading or inherited original-archive certificate.'})
    dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':40,'whole_root_files':43,'manifest_directories_including_dot':14,'source_blobs':10,'primary_pdf_text_pairs':3,'stable_named_originals':stable,'mutable_journal_observations':mutable,'artifact_cases':8,'negative_cases':6,'whole_actual_root_unchanged':True,'limits':'Artifact and existing bounded finite archive only,no full-scope mathematical/contribution grade.Verifier excludes modes;parent snapshot excludes rootmode.'})
    print(json.dumps({'files':43,'manifest_directories_including_dot':14,'sources':10,'primary_pairs':3,'stable_originals':14,'cases':8,'finite_diagnostic_matched':True}))
if __name__=='__main__':main()
