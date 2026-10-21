#!/usr/bin/env python3
"""Completed arithmetic116 byte archive; no mathematical execution or gate."""
import datetime,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r116'
spec=importlib.util.spec_from_file_location('archive_helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'e407953c41b61629054fa807ff5dcf125713bff162e0d798a26f9e56d60a25be','MANIFEST.json':'9e6849da5d97957c57e6aed913f05abc9008612716f5f4520afa93937eb5fc49','REPORT.md':'60987253cc83f97ad90763ba4e979e154d7173ab9f04fdd68ed24cf4c5965046'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
    now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P)
    assert len(read(B/'tasks.json')['tasks'])==510
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'initial_index_empty':True,'task_count':510,'task_index':508,'protected_unrelated_sha256':PROTECTED})
    before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current completed whole root excluding root-directory mode;no historical whole-project or OS certificate.'})
    st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and not st['hasPendingChildRuns'] and all(v in st['summary'] for v in ANCHORS.values())
    assert all(sha(ROOT/n)==v for n,v in ANCHORS.items())
    m=read(ROOT/'MANIFEST.json');assert m['schema']=='r116-exact-payload-v1' and len(m['files'])==94 and len(m['directories'])==11
    assert {p for p,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS) and {p for p,e in before.items() if e['kind']=='directory'}==set(m['directories'])
    for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
    tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    source=read(ROOT/'packet/source-identities.json');assert len(source)==47
    prefixes=['preprints/Exact-Birch-Swinnerton-Dyer-Formula-from-Low-Selmer-Corank-October-7-2026/','preprints/The-Selmer-converse-for-elliptic-curves-at-every-prime-October-7-2026/','preprints/The-two-primary-Birch-Swinnerton-Dyer-formula-in-Selmer-corank-at-most-one-October-6-2026/']
    assert {e['path'] for e in source}=={p for p,e in entries.items() if e['type']=='blob' and any(p.startswith(x) for x in prefixes) and not p.endswith('.pdf')}
    for e in source:
        data=(ROOT/e['local']).read_bytes();node=entries[e['path']]
        assert len(data)==e['size']==node['size'] and sha(ROOT/e['local'])==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['sha']==node['sha']
        assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
    primary=read(ROOT/'packet/primary-identities.json');assert len(primary)==5
    successes=[e for e in primary if 'sha256' in e];failures=[e for e in primary if 'failure' in e];assert len(successes)==2 and len(failures)==3
    for e in successes:
        p=ROOT/'packet/private/primary'/(e['name']+'.pdf');assert p.stat().st_size==e['size'] and sha(p)==e['sha256'] and sha(p.with_suffix('.txt'))==e['extract_sha256']
    stable=[];excerpts=[];incoming=read(ROOT/'packet/incoming-identities.json');assert len(incoming)==10
    for e in incoming:
        q=ROOT/e['selection'];assert q.stat().st_size==e['size'] and sha(q)==e['sha256'] and not e['inherited_manifest']
        if e['kind']=='whole current original copy':
            p=P/e['original'];assert p.read_bytes()==q.read_bytes();stable.append({'path':e['original'],'sha256':e['sha256'],'bytes':e['size'],'limit':'Late current whole-copy equality,not first-read or inherited whole-archive certification or fresh semantic reading.'})
        else:assert e['kind']=='retained excerpt of mutable current original';excerpts.append(e|{'limit':'Retained excerpt only;old whole observation is not a current/future original stability input.'})
    assert len(stable)==8 and len(excerpts)==2
    identities=read(ROOT/'packet/identity-checks.json');assert identities['canonical_source_blobs_checked']==47 and identities['complete_tree_entries']==13223
    assert len(identities['incoming_checks'])==10 and sum(e['same_as_capture'] for e in identities['incoming_checks'])==9
    assert [e['original'] for e in identities['incoming_checks'] if not e['same_as_capture']]==['frontier/NEW-TEN-2026-10-14.md']
    ctl=read(ROOT/'packet/control-results.json');fixture=ROOT/'packet/private/copied-controls';fm=read(fixture/'MANIFEST.json');assert len(ctl['results'])==7 and len(ctl['selection'])==3 and set(fm['files'])==set(ctl['selection'])
    for n,v in ctl['anchors'].items():assert sha(fixture/n)==v
    for n in ctl['selection']:assert (fixture/n).read_bytes()==(ROOT/n).read_bytes() and sha(fixture/n)==fm['files'][n]['sha256']
    assert all((e['returncode']==0)==e['expected_accept'] and e['snapshot_before']==e['snapshot_after'] for e in ctl['results'])
    cases=[]
    with tempfile.TemporaryDirectory(prefix='arithmetic116-copy-',dir=O) as temp:
        copy=Path(temp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),'--final',ANCHORS['FINAL.md'],'--manifest',ANCHORS['MANIFEST.json'],'--report',ANCHORS['REPORT.md']]
        def check(label,want,custom=None):
            state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'packet/tools/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
            assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state
            cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
        check('baseline_full_packet',True)
        p=copy/'packet/notes/quadratic-bsd-reduction.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('modified_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data)
        p=copy/'packet/private/.extra';p.write_text('extra');check('extra_hidden_file',False);p.unlink();p=copy/'packet/private/.empty';p.mkdir();check('extra_empty_directory',False);p.rmdir()
        wrong=args.copy();wrong[4]='0'*64;check('wrong_external_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
    assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in PROTECTED.items())
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':5,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Seven complete disposable-copy controls;the child seven selected-copy tests remain separate.Artifact evidence only.'})
    dump('input-authentication.json',{'source_blobs':47,'primary_pdf_files':2,'byte_bound_extracts':2,'byte_bound_renders':10,'historical_primary_failures':failures,'stable_whole_original_copies':8,'mutable_original_excerpts':2,'selected_fixture_members':3,'limits':'Canonical local bytes and retained-copy binding only,no fresh network/protected-body semantic/visual reading or inherited whole-archive certificate.'})
    dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':94,'whole_root_files':97,'subdirectories':11,'source_blobs':47,'primary_pdf_files':2,'stable_named_originals':stable,'mutable_original_excerpts':excerpts,'artifact_cases':7,'negative_cases':5,'whole_actual_root_unchanged':True,'limits':'Artifact archive only,no numerical/formal mathematical suite or independent correctness/contribution grade.Verifier excludes modes;parent snapshots exclude rootmode.'})
    print(json.dumps({'files':97,'subdirectories':11,'source_blobs':47,'primary_pdfs':2,'stable_whole_originals':8,'excerpts':2,'cases':7}))
if __name__=='__main__':main()
