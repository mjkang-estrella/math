#!/usr/bin/env python3
"""Completed no-nominee artifact archive; no analytic mathematical gate."""
import datetime,hashlib,importlib.util,io,json,shutil,subprocess,sys,tarfile,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-analytic-discovery-r144'
spec=importlib.util.spec_from_file_location('archive_helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'eac7aab7a39dd4b4930d0d34bd3de1429972e185b37abb0468144d3602d2eef1','MANIFEST.json':'5424e8c18de3b6daf8dfbe7a66dbb4a87f6561e3b4f29637c2b68e8b77eeb80d','REPORT.md':'2be704a3363439c6057fa7aa47e625dd7256f4495279a24e8f5dfea1174a928c'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
    now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P)
    assert len(read(B/'tasks.json')['tasks'])==505
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'initial_index_empty':True,'task_count':505,'task_index':502,'protected_unrelated_sha256':PROTECTED})
    before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current whole completed root,root-directory mode excluded; no historical whole-project or OS certificate.'})
    st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and not st['hasPendingChildRuns'] and all(v in st['summary'] for v in ANCHORS.values())
    assert all(sha(ROOT/n)==v for n,v in ANCHORS.items())
    m=read(ROOT/'MANIFEST.json');assert m['schema']=='r144-exact-payload-v1' and m['outside_envelopes']==sorted(ANCHORS) and len(m['files'])==52
    assert {p for p,e in before.items() if e['kind']=='file'}=={e['path'] for e in m['files']}|set(ANCHORS)
    for e in m['files']:assert (ROOT/e['path']).stat().st_size==e['size'] and sha(ROOT/e['path'])==e['sha256']
    tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    source=read(ROOT/'SOURCE-AUTH.json');assert source['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb' and source['tree_sha256']==sha(tp) and source['tree_entries']==13223 and len(source['files'])==14
    for e in source['files']:
        data=(ROOT/e['local']).read_bytes();node=entries[e['canonical_path']]
        assert len(data)==e['size']==node['size'] and sha(ROOT/e['local'])==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob_sha1']==node['sha']
        assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
    raw=members=failed=0
    for e in read(ROOT/'PRIMARY-AUTH.json'):
        assert e['url']=='https://arxiv.org/src/'+e['id']
        if 'failure' in e:assert e['id']=='1705.06831v2' and '404' in e['failure'];failed+=1;continue
        p=ROOT/'private/primary'/e['id'];data=(p/'incoming.bin').read_bytes();assert len(data)==e['incoming_size'] and hashlib.sha256(data).hexdigest()==e['incoming_sha256'];raw+=1
        with tarfile.open(fileobj=io.BytesIO(data)) as archive:
            for row in e['selected_members']:
                info=archive.getmember(row['name']);assert info.isfile();d=archive.extractfile(info).read();assert d==(p/'selected'/row['name']).read_bytes() and len(d)==row['size'] and hashlib.sha256(d).hexdigest()==row['sha256'];members+=1
        actual={x.relative_to(p/'selected').as_posix() for x in (p/'selected').rglob('*') if x.is_file()};assert actual=={x['name'] for x in e['selected_members']}
    assert (raw,members,failed)==(3,5,1)
    originals=read(ROOT/'LOCAL-ORIGINAL-AUTH.json');assert len(originals)==13;stable=[];mutable=[]
    for e in originals:
        if e['path']=='frontier/NEW-TEN-2026-10-14.md':mutable.append(e|{'current_sha256_observed':sha(P/e['path']),'limit':'Old mutable journal identity,not a current or post-append stability input; no retained body copy.'});continue
        assert (P/e['path']).stat().st_size==e['size'] and sha(P/e['path'])==e['sha256'];stable.append(e)
    assert len(stable)==12 and len(mutable)==1
    recheck=read(ROOT/'AUTH-RECHECK.json');assert [recheck[k] for k in ['tree_entries','source_blobs_matched','primary_incoming_archives_matched','primary_selected_members_matched','local_original_records_matched']]==[13223,14,3,5,13]
    ctl=read(ROOT/'CONTROL-RESULTS.json');fixture=ROOT/'private/control-fixture';fm=read(fixture/'MANIFEST.json');assert len(fm['files'])==1 and len(ctl['controls'])==6
    assert (fixture/'selected-note.md').read_bytes()==(ROOT/'GAPS.md').read_bytes() and sha(ROOT/'GAPS.md')==ctl['selected_original_sha256']
    assert fm['files'][0]['path']=='selected-note.md' and fm['files'][0]['sha256']==ctl['selected_original_sha256']
    for n,v in ctl['fixture_envelope_anchors'].items():assert sha(fixture/n)==v
    assert all((e['returncode']==0)==e['expected_accept'] for e in ctl['controls'])
    cases=[]
    with tempfile.TemporaryDirectory(prefix='analytic144-copy-',dir=O) as temp:
        copy=Path(temp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),'--final',ANCHORS['FINAL.md'],'--manifest',ANCHORS['MANIFEST.json'],'--report',ANCHORS['REPORT.md']]
        def check(label,want,custom=None):
            state=snap(copy);r=subprocess.run([sys.executable,'-B',str(copy/'verify.py'),*(custom or args)],text=True,capture_output=True,timeout=30)
            assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state
            cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
        check('baseline_full_packet',True)
        p=copy/'LOCALIZATION-DETAILS.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('modified_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data)
        p=copy/'private/.extra';p.write_text('extra');check('extra_hidden_file',False);p.unlink();wrong=args.copy();wrong[4]='0'*64;check('wrong_external_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
    assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in PROTECTED.items())
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':4,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Six full-copy controls;child six selected-copy controls remain historical. No math gate.'})
    dump('input-authentication.json',{'source_blobs':14,'primary_raw_archives':3,'selected_members':5,'failed_primary_requests':1,'stable_originals':12,'mutable_journal':1,'retained_original_copies':0,'limits':'Source/tree/blob and raw/member binding only,not fresh protected-body semantic or remote identity reading.'})
    dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':52,'whole_root_files':55,'directories':sum(e['kind']=='directory' for e in before.values()),'source_blobs':14,'primary_raw_archives':3,'selected_primary_members':5,'stable_named_originals':stable,'mutable_journal_observations':mutable,'artifact_cases':6,'negative_cases':4,'whole_actual_root_unchanged':True,'limits':'Artifact archive only,no PDE/analytic/contribution grade or invented numerical suite. Verifier excludes modes/emptydirs/hardlinkpolicy;parent snapshots include current modes/links but exclude rootmode.'})
    print(json.dumps({'files':55,'directories':sum(e['kind']=='directory' for e in before.values()),'sources':14,'raw_archives':3,'members':5,'stable_originals':12,'cases':6}))
if __name__=='__main__':main()
