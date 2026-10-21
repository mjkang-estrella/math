#!/usr/bin/env python3
"""Completed structural150 archive; bounded diagnostic safely rebound to a copy."""
import datetime,hashlib,importlib.util,json,shutil,stat,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r150'
spec=importlib.util.spec_from_file_location('archive_helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha=h.sha
def snap(root):
    s=h.snap(root);s['']={'kind':'directory','mode':stat.S_IMODE(root.lstat().st_mode)};return s
ANCHORS={'FINAL.md':'09d28e5fa7a855648ca03618582728b555fc2be0612efd85ba78c4d8f0eeb5fd','MANIFEST.json':'2fdd134047cdb76fecce2d5a78f2df229dcb03af81e5a88368b4a1942568b17d','REPORT.md':'2c55911a0ab6ac1e6506e3421f97f3fa2915443b3179a15b32c8840281f207e2'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
    now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P)
    assert len(read(B/'tasks.json')['tasks'])==507
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'initial_index_empty':True,'task_count':507,'task_index':504,'protected_unrelated_sha256':PROTECTED})
    before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current completed root including root mode under the empty root key; no historic whole-project or OS certificate.'})
    st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and not st['hasPendingChildRuns'] and all(v in st['summary'] for v in ANCHORS.values())
    assert all(sha(ROOT/n)==v for n,v in ANCHORS.items())
    m=read(ROOT/'MANIFEST.json');assert m['schema']=='r150-exact-payload-v1' and m['envelopes']==sorted(ANCHORS) and len(m['payload'])==57 and len(m['directories'])==19
    assert {p for p,e in before.items() if e['kind']=='file'}==set(m['payload'])|set(ANCHORS) and {p for p,e in before.items() if e['kind']=='directory'}==set(m['directories'])
    for n,e in m['payload'].items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
    assert (ROOT/'FINAL.md').read_bytes()==(ROOT/'notes/final-envelope.txt').read_bytes() and (ROOT/'REPORT.md').read_bytes()==(ROOT/'notes/report-envelope.txt').read_bytes()
    tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    a=read(ROOT/'private/source-authentication.json');assert a['tree_sha256']==sha(tp) and a['entries']==13223 and len(a['files'])==12
    source=a['files']+[read(ROOT/'private/companion-authentication.json')|{'local':'private/companion113.tex'}]
    for e in source:
        data=(ROOT/e['local']).read_bytes();node=entries[e['canonical_path']]
        assert len(data)==e['size']==node['size'] and sha(ROOT/e['local'])==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha']
        assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
    primary=read(ROOT/'private/primary/receipts.json');assert len(primary)==6
    for e in primary:
        p=ROOT/'private/primary'/(e['name']+'.pdf');assert p.stat().st_size==e['size'] and sha(p)==e['sha256'] and sha(p.with_suffix('.txt'))==e['text_sha256']
    stable=[];mutable=[];originals=read(ROOT/'private/incoming-originals.json')['records'];assert len(originals)==13
    for e in originals:
        if e['path']=='frontier/NEW-TEN-2026-10-14.md':mutable.append(e|{'current_sha256_observed':sha(P/e['path']),'limit':'Mutable journal old identity is not a current or post-append stability input.'});continue
        assert (P/e['path']).stat().st_size==e['size'] and sha(P/e['path'])==e['sha256'];stable.append(e)
    assert len(stable)==12 and len(mutable)==1
    ctl=read(ROOT/'private/controls/results.json');fixture=ROOT/'private/controls/selected-copy';fm=read(fixture/'MANIFEST.json');assert len(ctl['controls'])==7 and len(ctl['selected_original_hashes'])==4
    assert set(fm['payload'])==set(ctl['selected_original_hashes'])
    for n,v in ctl['detached_copy_anchors'].items():assert sha(fixture/n)==v
    for n,v in ctl['selected_original_hashes'].items():assert sha(fixture/n)==sha(ROOT/n)==v==fm['payload'][n]['sha256']
    assert [e['accepted'] for e in ctl['controls']]==[True,False,False,False,False,False,True]
    cases=[]
    with tempfile.TemporaryDirectory(prefix='structural150-copy-',dir=O) as temp:
        copy=Path(temp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),'--final',ANCHORS['FINAL.md'],'--manifest',ANCHORS['MANIFEST.json'],'--report',ANCHORS['REPORT.md']]
        def check(label,want,custom=None):
            state=snap(copy);r=subprocess.run([sys.executable,'-B',str(copy/'code/verify.py'),*(custom or args)],text=True,capture_output=True,timeout=30)
            assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state
            cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
        check('baseline_full_packet',True)
        p=copy/'notes/02-integrated-reduction-and-gap.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('modified_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data)
        p=copy/'private/.extra';p.write_text('extra');check('extra_hidden_file',False);p.unlink();p=copy/'private/.empty';p.mkdir();check('extra_empty_directory',False);p.rmdir()
        wrong=args.copy();wrong[4]='0'*64;check('wrong_external_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
        source_text=(copy/'code/core_diagnostic.py').read_text();assignment='R=Path('+repr(str(ROOT))+')'
        assert source_text.count(assignment)==1 and source_text.count(str(ROOT))==1
        rebound=source_text.replace(assignment,'R=Path('+repr(str(copy))+')',1)
        state=snap(copy);r=subprocess.run([sys.executable,'-B','-c',rebound],capture_output=True,text=True,check=True,timeout=45)
        diag=json.loads(r.stdout);assert diag==read(ROOT/'notes/finite-diagnostic.json') and snap(copy)==state
    rows=diag['core_and_unicyclic_checks'];assert sum(e['graphs_checked'] for e in rows)==33864 and sum(e['core_fibers'] for e in rows)==23864 and sum(e['unicyclic_degree_vectors'] for e in rows)==476
    assert diag['parent_maps']==878 and diag['parent_count_fibers']==170
    assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in PROTECTED.items())
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':5,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Seven full-copy integrity controls;child selected-copy controls remain separate. No mathematical gate.'})
    dump('diagnostic-replay.json',{'original_diagnostic_sha256':sha(ROOT/'code/core_diagnostic.py'),'only_source_change_for_execution':'The unique hardcoded R assignment rebound to disposable complete copy; original and copied program files unchanged.','diagnostic':diag,'copied_root_bytes_modes_links_unchanged_after_regeneration':True,'limits':'Writer runs only in disposable copy,not directly against hardcoded sealed original. Identical final bytes do not mean zero writes. Finite calculations only,no general sampler or mixing proof.'})
    dump('input-authentication.json',{'source_blobs':13,'source131_files':12,'source113_companion_files':1,'primary_pdf_text_pairs':6,'byte_bound_renders':2,'stable_originals':12,'mutable_journal':1,'retained_external_original_copies':0,'selected_fixture_files':4,'limits':'Current named original hashes and source/copy metadata only,no fresh protected-body semantic/network/visual reading or historic whole-original certificate.'})
    dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':57,'whole_root_files':60,'directories_including_root':19,'source_blobs':13,'primary_pdf_text_pairs':6,'stable_named_originals':stable,'mutable_journal_observations':mutable,'artifact_cases':7,'negative_cases':5,'graphs_checked':33864,'core_fibers_checked':23864,'unicyclic_degree_vectors':476,'parent_maps':878,'parent_count_fibers':170,'whole_actual_root_unchanged':True,'limits':'Artifact and bounded finite calculation only,no independent math/contribution grade or universal mixing/weighted-core sampler. Verifier excludes modes;parent snapshots include rootmode.'})
    print(json.dumps({'files':60,'directories_including_root':19,'sources':13,'primary_pairs':6,'stable_originals':12,'cases':7,'graphs':33864,'core_fibers':23864,'parent_maps':878}))
if __name__=='__main__':main()
