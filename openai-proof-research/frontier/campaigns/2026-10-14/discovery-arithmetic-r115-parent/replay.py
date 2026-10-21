#!/usr/bin/env python3
"""Completed arithmetic115 artifact archive; no mathematical execution or gate."""
import datetime,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r115'
spec=importlib.util.spec_from_file_location('archive_helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'5ccdf50c6dfcf05a359471b38e754bf5646eda87d69f5562116818e09c428185','MANIFEST.json':'96f49938b8b074b62c963a841e6464ab3c81f73f1c36a51b7b3a9e7676982d03','REPORT.md':'af052321664e09d862f0b75e49be9588b76b2b26e69964d70d003595d87e9402'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
    now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P)
    assert len(read(B/'tasks.json')['tasks'])==508
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'initial_index_empty':True,'task_count':508,'task_index':506,'protected_unrelated_sha256':PROTECTED})
    before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current complete completed root snapshot excluding root-directory mode; no historical whole-project or OS certificate.'})
    st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and not st['hasPendingChildRuns'] and all(v in st['summary'] for v in ANCHORS.values())
    assert all(sha(ROOT/n)==v for n,v in ANCHORS.items())
    m=read(ROOT/'MANIFEST.json');assert m['format']=='r115-exact-v1' and m['outside_envelopes']==list(ANCHORS) and len(m['files'])==61 and len(m['directories'])==21
    assert {p for p,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS) and {p for p,e in before.items() if e['kind']=='directory'}==set(m['directories'])
    for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['bytes'] and sha(ROOT/n)==e['sha256']
    tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    source=read(ROOT/'packet/source-identities.json');assert len(source)==20
    prefixes=['preprints/The-p-adic-section-conjecture-October-6-2026/','preprints/Etale-covers-with-a-prescribed-exterior-sheet-September-24-2026/']
    selected={p for p,e in entries.items() if e['type']=='blob' and any(p.startswith(x) for x in prefixes) and not p.endswith('.pdf')};assert {e['path'] for e in source}==selected
    for e in source:
        data=(ROOT/e['copy']).read_bytes();node=entries[e['path']]
        assert e['copy']=='packet/private/source/'+e['path'] and len(data)==e['size']==node['size'] and sha(ROOT/e['copy'])==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha']
        assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
    primary=read(ROOT/'packet/private/primary/identities.json');assert len(primary)==2
    for e in primary:
        p=ROOT/'packet/private/primary'/e['file'];assert p.stat().st_size==e['size'] and sha(p)==e['sha256'] and str(p.with_suffix('.txt').relative_to(ROOT)) in m['files']
    incoming=read(ROOT/'packet/incoming-identities.json');assert incoming['tree']['entries']==13223 and incoming['tree']['sha256']==sha(tp) and incoming['tree']['truncated'] is False
    stable=[];excerpts=[];assert len(incoming['items'])==12
    for e in incoming['items']:
        q=ROOT/e['copy'];assert sha(q)==e['sha256']
        if e['kind']=='whole-current-copy':
            p=P/e['original'];assert q.stat().st_size==e['bytes'] and p.read_bytes()==q.read_bytes();stable.append({'path':e['original'],'sha256':sha(p),'bytes':p.stat().st_size,'limit':'Late current whole-original/copy equality,not first-read or whole-original-archive certification and not fresh semantic reading.'})
        else:assert e['kind']=='excerpt';excerpts.append(e|{'limit':'Retained selected excerpt only;old whole observed identity is not a current or future stability input.'})
    assert len(stable)==10 and len(excerpts)==2
    ctl=read(ROOT/'packet/private/controls/receipt.json');fixture=ROOT/'packet/private/controls/fixture';fm=read(fixture/'MANIFEST.json');assert len(ctl['cases'])==7 and len(ctl['selected_from_r115'])==3 and set(fm['files'])==set(ctl['selected_from_r115'])
    for n,v in ctl['fixture_envelope_anchors'].items():assert sha(fixture/n)==v
    for n in ctl['selected_from_r115']:assert (fixture/n).read_bytes()==(ROOT/n).read_bytes() and sha(fixture/n)==fm['files'][n]['sha256']
    assert all((e['returncode']==0)==e['expected_accept'] for e in ctl['cases'])
    cases=[]
    with tempfile.TemporaryDirectory(prefix='arithmetic115-copy-',dir=O) as temp:
        copy=Path(temp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),*ANCHORS.values()]
        def check(label,want,custom=None):
            state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'packet/tools/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
            assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state
            cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
        check('baseline_full_packet',True)
        p=copy/'packet/notes/affine-reduction.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('modified_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data)
        p=copy/'packet/private/.extra';p.write_text('extra');check('extra_hidden_file',False);p.unlink();p=copy/'packet/private/.empty';p.mkdir();check('extra_empty_directory',False);p.rmdir()
        wrong=args.copy();wrong[2]='0'*64;check('wrong_external_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
    assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in PROTECTED.items())
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':5,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Seven complete disposable-copy controls;the original seven selected-copy tests remain separate. Artifact evidence only.'})
    dump('input-authentication.json',{'source_blobs':20,'primary_pdf_files':2,'byte_bound_matching_stem_extracts':2,'byte_bound_renders':2,'stable_whole_original_copies':10,'mutable_original_excerpts':2,'selected_fixture_members':3,'limits':'Local canonical source/blob and retained-copy checks only,no fresh network,protected-body semantic or visual reading and no inherited whole-archive certificate.'})
    dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':61,'whole_root_files':64,'directories':21,'source_blobs':20,'primary_pdf_files':2,'stable_named_originals':stable,'mutable_original_excerpts':excerpts,'artifact_cases':7,'negative_cases':5,'whole_actual_root_unchanged':True,'limits':'Artifact archive only,no numerical/formal mathematical suite or independent correctness/contribution grade. Verifier excludes modes,parent snapshots exclude rootmode.'})
    print(json.dumps({'files':64,'directories':21,'source_blobs':20,'primary_pdfs':2,'stable_whole_originals':10,'excerpts':2,'cases':7}))
if __name__=='__main__':main()
