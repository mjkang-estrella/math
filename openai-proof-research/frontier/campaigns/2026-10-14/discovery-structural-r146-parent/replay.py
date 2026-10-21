#!/usr/bin/env python3
"""Parent artifact and exact finite-diagnostic replay; no mathematical gate."""
import datetime,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
from fractions import Fraction as F
from pathlib import Path
OUT=Path(__file__).resolve().parent;BASE=OUT.parent;PROJECT=BASE.parents[2];ROOT=BASE/'fresh-structural-discovery-r146'
spec=importlib.util.spec_from_file_location('archive_helpers',BASE/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
sha,snap=helper.sha,helper.snap
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
ANCHORS={'FINAL.md':'1edc2f869d891319399844487ad433bdfaf298ba08b7680da86e20a735dcc602','MANIFEST.json':'2bf4ffdcfdeef1dfee627acbb56f733e73c7b53a376e9fc75c2052199ce029c2','REPORT.md':'c0c0db9433b6fa202ee0acb5a7e8b9f436e4c2f6a40d8572fbdef5c2df98cac1'}
def dump(n,d):(OUT/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
    assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=PROJECT)
    assert all(sha(PROJECT/p)==h for p,h in PROTECTED.items())
    now=datetime.datetime.now(datetime.timezone.utc).isoformat()
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=PROJECT,text=True).strip(),'initial_index_empty':True,'task_count':492,'task_index':488,'protected_unrelated_sha256':PROTECTED})
    before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current whole actual root, not historical whole-parent or OS evidence.'})
    assert all(sha(ROOT/p)==h for p,h in ANCHORS.items())
    terminal=json.loads((OUT/'task-status.json').read_text())['structuredContent']
    assert terminal['status']=='completed' and all(h in terminal['summary'] for h in ANCHORS.values())
    m=json.loads((ROOT/'MANIFEST.json').read_text());assert m['format']=='r146-exact-membership-v1'
    files=m['files'];dirs=m['directories'];assert len(files)==63 and len(dirs)==23
    assert {p for p,e in before.items() if e['kind']=='file'}==set(files)|set(ANCHORS)
    assert {p for p,e in before.items() if e['kind']=='directory'}==set(dirs)
    assert all(e['kind'] in ['file','directory'] and (e['kind']!='file' or e['nlink']==1) for e in before.values())
    for p,e in files.items():assert sha(ROOT/p)==e['sha256'] and (ROOT/p).stat().st_size==e['size']
    tp=PROJECT/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree=json.loads(tp.read_text());assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    sources=json.loads((ROOT/'private/pinned-receipts.json').read_text());assert len(sources)==17
    for e in sources:
        data=(ROOT/e['local']).read_bytes();node=entries[e['path']]
        assert len(data)==e['size']==node['size'] and sha(ROOT/e['local'])==e['sha256']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['gitblob']==node['sha']
        assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
    primary=json.loads((ROOT/'private/primary/receipts.json').read_text());assert len(primary)==3
    for e in primary:
        p=ROOT/e['path'];assert sha(p)==e['sha256'] and p.stat().st_size==e['size']
        assert p.with_suffix('.txt').relative_to(ROOT).as_posix() in files
    copies=json.loads((ROOT/'private/selected-originals-receipts.json').read_text());assert len(copies)==13
    stable=[]
    for e in copies:
        p=PROJECT/e['original'];q=ROOT/e['snapshot']
        assert p.read_bytes()==q.read_bytes() and sha(p)==sha(q)==e['sha256'] and p.stat().st_size==e['size']
        stable.append({'path':e['original'],'sha256':e['sha256'],'size':e['size'],'limit':e['status']})
    cases=[]
    with tempfile.TemporaryDirectory(prefix='structural146-copy-',dir=OUT) as temp:
        copy=Path(temp)/'packet';shutil.copytree(ROOT,copy)
        args=[str(copy),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']]
        def check(label,expected,custom=None):
            state=snap(copy);r=subprocess.run([sys.executable,'-B',str(copy/'scripts/verify_packet.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
            assert (r.returncode==0)==expected,(label,r.stdout,r.stderr)
            assert snap(copy)==state
            cases.append({'case':label,'expected_pass':expected,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
        check('baseline_full_packet',True)
        p=copy/'notes/01-prefreeze-derivation.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('modified_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data)
        p=copy/'private/.extra';p.write_text('extra');check('extra_hidden_payload',False);p.unlink()
        p=copy/'private/.extra-empty';p.mkdir();check('extra_empty_directory',False);p.rmdir()
        wrong=args.copy();wrong[4]='0'*64;check('wrong_external_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
        state=snap(copy)
        result=subprocess.run([sys.executable,'-B',str(copy/'scripts/signature_diagnostic.py')],capture_output=True,text=True,check=True,timeout=30)
        diagnostic=json.loads(result.stdout);assert diagnostic==json.loads((ROOT/'private/signature-diagnostic.json').read_text()) and snap(copy)==state
        assert diagnostic['weighted_shift_cases']==28 and diagnostic['adjacent_checks']==1344
    # Independent exact values from the displayed toy weight, not a floating inertia calculation.
    unit=[(1,0,0),(0,1,0),(0,0,1)]
    Q=[[F(2)**(-(unit[i][0]+unit[j][0]-unit[i][1]-unit[j][1])**2) for j in range(3)] for i in range(3)]
    assert [[str(x) for x in row] for row in Q]==diagnostic['matrix']
    a=Q[0][0]+Q[1][1]+2*Q[0][1];b=Q[0][2]+Q[1][2];c=Q[2][2]
    assert a*c-b*b==F(9,8) and Q[0][0]+Q[1][1]-2*Q[0][1]==F(-15,8)
    assert a*c*F(9,10)**2-b*b*F(11,10)**2==F(409,800)
    bases={frozenset((i,j)) for i in (1,2) for j in (3,4)}
    slab={x for x in bases if len(x&{1,3})<=1};equal={x for x in bases if len(x&{1,3})==1}
    assert slab=={frozenset(x) for x in [(1,4),(2,3),(2,4)]} and equal=={frozenset((1,4)),frozenset((2,3))}
    for family in [slab,equal]:
        x,y=frozenset((1,4)),frozenset((2,3));assert all((x-{4})|{z} not in family for z in y-x)
    assert snap(ROOT)==before and all(sha(PROJECT/e['path'])==e['sha256'] for e in stable)
    assert all(sha(PROJECT/p)==h for p,h in PROTECTED.items())
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':5,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Complete copied packet byte controls only; no mathematical gates.'})
    dump('diagnostic-replay.json',{'actual_copied_script_result':diagnostic,'copied_root_unchanged_after_diagnostic':True,'independent_toy_weight_matrix_and_determinants_checked':True,'independent_slab_and_equality_exchange_failure_checked':True,'limits':'Exact finite supporting diagnostics only; not a full counting algorithm or independent proof/contribution review.'})
    dump('input-authentication.json',{'source_blobs':17,'complete_canonical_tree_bound_independently':True,'primary_pdf_text_pairs':3,'render_files_bound_by_manifest':4,'selected_copy_members':copies,'stable_named_originals':stable,'limits':'Late current selected bytes, separate from selected-copy membership. No whole incoming packet, first-read, fresh source/primary/history semantics, PDF visual or historical whole-parent certificate.'})
    dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'verifier_sha256':sha(ROOT/'scripts/verify_packet.py'),'payload_files':63,'whole_root_files':66,'directories':23,'source_blobs':17,'primary_pdf_text_pairs':3,'stable_named_originals':stable,'selected_copy_members':13,'artifact_cases':7,'negative_cases':5,'weighted_shift_cases':28,'adjacent_checks':1344,'whole_actual_root_unchanged':True,'stable_originals_unchanged':True,'limits':'Artifact bytes and exact finite supporting diagnostics only; no frozen theorem/nominee, mathematical/contribution grade, fresh semantic primary/history reading or historical whole-parent/OS certificate.'})
    print(json.dumps({'payloads':63,'whole_files':66,'directories':23,'source_blobs':17,'primary_pairs':3,'stable_originals_and_whole_copies':13,'artifact_cases':7,'negative_cases':5,'weighted_shift_cases':28,'adjacent_checks':1344,'whole_root_unchanged':True}))
if __name__=='__main__':main()
