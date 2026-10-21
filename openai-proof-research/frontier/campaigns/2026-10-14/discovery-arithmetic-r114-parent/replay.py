#!/usr/bin/env python3
"""Completed arithmetic114 integrity and bounded local-algebra replay."""
import datetime,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r114';PK=ROOT/'packet'
spec=importlib.util.spec_from_file_location('archive_helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'519a7926a56d776dad6b5f85387340cf360929259d83350c6a624cbe12e62d26','MANIFEST.json':'0ace5139d7d4d0a4ed9ae7c5766c253334f4dbfb1558dfa65af6822476e3ae79','REPORT.md':'b57f3fb34a1f483cb6dd0f6c26faf5c44b04bd94f6d77fda5dda63d3f88eb9a2'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
    now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P)
    assert len(read(B/'tasks.json')['tasks'])==506
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'initial_index_empty':True,'task_count':506,'task_index':503,'protected_unrelated_sha256':PROTECTED})
    before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current complete root snapshot excluding root-directory mode; no historical whole-project or OS certificate.'})
    st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and not st['hasPendingChildRuns'] and all(v in st['summary'] for v in ANCHORS.values())
    assert all(sha(ROOT/n)==v for n,v in ANCHORS.items())
    m=read(ROOT/'MANIFEST.json');assert m['schema']=='r114-exact-v1' and m['kind']=='research' and m['envelopes']==sorted(ANCHORS) and len(m['files'])==58 and len(m['directories'])==14
    assert {p for p,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS) and {p for p,e in before.items() if e['kind']=='directory'}==set(m['directories'])
    for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
    tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'==sha(PK/'private/history/02-preprints-tree.json')
    tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    source=read(PK/'private/source/authentication.json');assert len(source)==13
    prefix='preprints/Integral-points-on-character-varieties-of-curves-September-25-2026/'
    expected={p for p,e in entries.items() if p.startswith(prefix) and e['type']=='blob' and p.endswith(('.md','.tex','.bib'))};assert {e['path'] for e in source}==expected
    for e in source:
        p=PK/'private/source'/e['local'];data=p.read_bytes();node=entries[e['path']]
        assert e['path']==prefix+e['local'] and len(data)==e['size']==node['size'] and sha(p)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha']
        assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
    primary=read(PK/'private/primary/acquisition.json');assert len(primary)==2
    for e in primary:
        p=PK/'private/primary'/e['file'];assert p.stat().st_size==e['size'] and sha(p)==e['sha256'] and str(p.with_suffix('.txt').relative_to(ROOT)) in m['files']
    originals=read(PK/'incoming-authentication.json');assert len(originals)==15;stable=[];excerpt=[]
    for e in originals:
        q=ROOT/e['copy'];assert sha(q)==e.get('sha256',e.get('excerpt_sha256'))
        if e['whole_copy']:
            p=P/e['original'];assert q.stat().st_size==e['size'] and p.read_bytes()==q.read_bytes();stable.append({'path':e['original'],'sha256':sha(p),'size':p.stat().st_size,'limit':'Late current whole-original/copy check,not first-read or whole-incoming packet certification; no fresh semantic reading.'})
        else:excerpt.append(e|{'limit':'Mutable journal retained excerpt; old observed whole hash is not a current stability input.'})
    assert len(stable)==14 and len(excerpt)==1
    ctl=read(ROOT/'controls/receipt.json');fixture=ROOT/'controls/fixture';fm=read(fixture/'MANIFEST.json');assert fm['kind']=='synthetic-control' and len(ctl['cases'])==7
    for n,v in ctl['anchors'].items():assert sha(fixture/n)==v
    for n,e in fm['files'].items():assert (fixture/n).stat().st_size==e['size'] and sha(fixture/n)==e['sha256']
    assert set(fm['files'])=={'packet/a.txt','packet/verify.py'} and (fixture/'packet/verify.py').read_bytes()==(PK/'tools/verify.py').read_bytes()
    assert all((e['exit_code']==0)==e['expected_pass'] for e in ctl['cases'])
    cases=[]
    with tempfile.TemporaryDirectory(prefix='arithmetic114-copy-',dir=O) as temp:
        copy=Path(temp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),'--final',ANCHORS['FINAL.md'],'--manifest',ANCHORS['MANIFEST.json'],'--report',ANCHORS['REPORT.md']]
        def check(label,want,custom=None):
            state=snap(copy);r=subprocess.run([sys.executable,'-B',str(copy/'packet/tools/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
            assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state
            cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
        check('baseline_full_packet',True)
        p=copy/'packet/notes/symplectic-reduction.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('modified_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data)
        p=copy/'packet/private/.extra';p.write_text('extra');check('extra_hidden_file',False);p.unlink();p=copy/'packet/private/.empty';p.mkdir();check('extra_empty_directory',False);p.rmdir()
        wrong=args.copy();wrong[4]='0'*64;check('wrong_external_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
        state=snap(copy);r=subprocess.run([sys.executable,'-B',str(copy/'packet/tools/local_diagnostic.py')],capture_output=True,text=True,check=True,timeout=45);diag=json.loads(r.stdout);assert diag==read(PK/'notes/local-diagnostic.json') and snap(copy)==state
    assert sum(e['ordered_pairs'] for e in diag['line_parabolic'])==16418 and diag['higher_block_integer_cases']==81
    assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in PROTECTED.items())
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':5,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Seven full complete-copy controls; original seven synthetic controls are separate historical evidence. No math gate.'})
    dump('diagnostic-replay.json',{'diagnostic':diag,'copied_root_unchanged':True,'limits':'16418 finite ordered pairs and81 integer block examples on disposable complete copy. No relative weighted reconstruction or global density proof.'})
    dump('input-authentication.json',{'source_blobs':13,'primary_pdf_files':2,'byte_bound_matching_stem_extracts':2,'byte_bound_renders':2,'stable_whole_original_copies':14,'mutable_excerpt_copies':1,'limits':'Canonical source/blob and retained-copy membership checks; no fresh remote/source/primary semantic or visual reading, and no inherited original packet certificate.'})
    dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':58,'whole_root_files':61,'directories':14,'source_blobs':13,'primary_pdf_files':2,'stable_named_originals':stable,'mutable_excerpt_copies':excerpt,'artifact_cases':7,'negative_cases':5,'finite_ordered_pair_checks':16418,'integer_block_checks':81,'whole_actual_root_unchanged':True,'limits':'Artifact and bounded finite support only;no independent math/contribution grade or universal reconstruction proof. Verifier excludes modes,parent snapshot excludes rootmode.'})
    print(json.dumps({'files':61,'directories':14,'sources':13,'primary_pdfs':2,'stable_whole_originals':14,'cases':7,'finite_pairs':16418,'integer_blocks':81}))
if __name__=='__main__':main()
