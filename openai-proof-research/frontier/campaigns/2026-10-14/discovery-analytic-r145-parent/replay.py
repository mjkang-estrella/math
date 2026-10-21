#!/usr/bin/env python3
"""Completed analytic145 byte archive; no analytic or contribution gate."""
import datetime, gzip, hashlib, importlib.util, io, json, shutil, subprocess, sys, tarfile, tempfile
from pathlib import Path

O=Path(__file__).resolve().parent; B=O.parent; P=B.parents[2]; ROOT=B/'fresh-analytic-discovery-r145'
spec=importlib.util.spec_from_file_location('archive_helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py')
h=importlib.util.module_from_spec(spec); spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'05b8efda2a591ee41dc17a475a86f4189de155345926f866cc06a2547f8b9d5d','MANIFEST.json':'ff1d6c6e4bea8d51b6ef2d376a3badae889d83aa098b0da9d4f1fd614a5671c1','REPORT.md':'c10b53741f77544ace9392b345302afca54501807a7f9a5ecdcc43ac9d4f5e9f'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p): return json.loads(p.read_text())
def dump(n,d): (O/n).write_text(json.dumps(d,indent=2)+'\n')
def digest(b): return hashlib.sha256(b).hexdigest()

def main():
    now=datetime.datetime.now(datetime.timezone.utc).isoformat()
    assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P)
    assert len(read(B/'tasks.json')['tasks'])==509
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'initial_index_empty':True,'task_count':509,'task_index':505,'protected_unrelated_sha256':PROTECTED})
    before=snap(ROOT)
    dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current completed whole root,root-directory mode excluded;no historical whole-project or OS certificate.'})
    st=read(O/'task-status.json')['structuredContent']
    assert st['status']=='completed' and not st['hasPendingChildRuns'] and all(v in st['summary'] for v in ANCHORS.values())
    assert all(sha(ROOT/n)==v for n,v in ANCHORS.items())
    m=read(ROOT/'MANIFEST.json'); assert len(m['files'])==57
    assert {p for p,e in before.items() if e['kind']=='file'}=={e['path'] for e in m['files']}|set(ANCHORS)
    for e in m['files']: assert (ROOT/e['path']).stat().st_size==e['size'] and sha(ROOT/e['path'])==e['sha256']
    tp=P/'sources/preprints-tree.json'
    assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree=read(tp); assert len(tree['tree'])==13223 and not tree['truncated']; entries={e['path']:e for e in tree['tree']}
    source=read(ROOT/'SOURCE-AUTH.json'); assert len(source)==11
    prefix='preprints/A-counterexample-to-the-Monge-ansatz-for-the-three-marginal-Coulomb-cost-September-25-2026/'
    assert {e['path'] for e in source}=={p for p,e in entries.items() if p.startswith(prefix) and e['type']=='blob' and not p.endswith('.pdf')}
    for e in source:
        data=(ROOT/e['selected_copy']).read_bytes(); node=entries[e['path']]
        assert e['selected_copy']=='private/source/'+e['path'][len(prefix):]
        assert len(data)==e['size']==node['size'] and digest(data)==e['sha256']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha']
        assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
    raw=members=tar_matches=0; failures=[]
    for e in read(ROOT/'PRIMARY-AUTH.json'):
        if 'failure' in e: failures.append({'id':e['id'],'failure':e['failure']}); continue
        ident=e['id'].replace('-decoding-recovery','')
        p=ROOT/'private/primary'/ident/'incoming.bin'
        if ident=='CDM2013-author-April11': p=ROOT/'private/primary/CDM2013/MultiColDim.pdf'
        data=p.read_bytes(); assert len(data)==e['incoming_size'] and digest(data)==e['incoming_sha256']; raw+=1
        for row in e['members']:
            d=(ROOT/row['selected_path']).read_bytes()
            assert len(d)==row['size'] and digest(d)==row['sha256']; members+=1
            if row.get('archive_member'):
                with tarfile.open(fileobj=io.BytesIO(data),mode='r:*') as archive:
                    info=archive.getmember(row['archive_member']); assert info.isfile() and archive.extractfile(info).read()==d
                tar_matches+=1
        if ident=='1907.08425v1':
            d=gzip.decompress(data)
            assert d==(ROOT/'private/primary/1907.08425v1/selected-original.tex').read_bytes()
            assert d.decode('latin1').encode('utf8')==(ROOT/'private/primary/1907.08425v1/reading-latin1.txt').read_bytes()
        if ident=='1608.08780v1': assert gzip.decompress(data)==(ROOT/'private/primary/1608.08780v1/selected.tex').read_bytes()
    assert (raw,members,tar_matches)==(7,13,8) and len(failures)==2
    assert {e['id'] for e in failures}=={'1907.08425v1','BCD-revised-author'}
    originals=read(ROOT/'ORIGINAL-AUTH.json')['files']; assert len(originals)==23
    stable=[]; mutable=[]
    for e in originals:
        if e['path']=='frontier/NEW-TEN-2026-10-14.md':
            mutable.append(e|{'parent_current_sha256_observed':sha(P/e['path']),'limit':'Old mutable journal identity,not a current/future stability input;no retained original body.'}); continue
        assert (P/e['path']).stat().st_size==e['size'] and sha(P/e['path'])==e['sha256']; stable.append(e)
    assert len(stable)==22 and len(mutable)==1
    recheck=read(ROOT/'AUTH-RECHECK.json')
    assert [recheck[k] for k in ['complete_tree_entries','source_blobs_matched','primary_incoming_matched','primary_selected_or_derivative_hashes_matched','selected_tar_members_compared_to_incoming_in_memory','named_originals_recorded']]==[13223,11,7,13,8,23]
    ctl=read(ROOT/'CONTROLS.json'); fixture=ROOT/'private/control-fixture'; fm=read(fixture/'MANIFEST.json')
    assert len(ctl['cases'])==6 and len(fm['files'])==1
    assert (fixture/'selected-prose.md').read_bytes()==(ROOT/'GAPS.md').read_bytes()
    row=fm['files'][0]; assert row['path']=='selected-prose.md' and row['sha256']==sha(ROOT/'GAPS.md') and row['size']==(ROOT/'GAPS.md').stat().st_size
    for n,v in ctl['fixture_anchors'].items(): assert sha(fixture/n)==v
    assert all((e['returncode']==0)==e['expected_accept'] for e in ctl['cases'])
    cases=[]
    with tempfile.TemporaryDirectory(prefix='analytic145-copy-',dir=O) as temp:
        copy=Path(temp)/'packet'; shutil.copytree(ROOT,copy)
        args=['--root',str(copy),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']]
        def check(label,want,custom=None):
            state=snap(copy)
            r=subprocess.run([sys.executable,'-I','-B',str(copy/'verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
            assert (r.returncode==0)==want,(label,r.stdout,r.stderr); assert snap(copy)==state
            cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
        check('baseline_full_packet',True)
        p=copy/'DERIVATION.md'; data=p.read_bytes(); p.write_bytes(data+b'\nCONTROL\n'); check('modified_payload',False)
        p.unlink(); check('missing_payload',False); p.write_bytes(data)
        p=copy/'private/.extra'; p.write_text('extra'); check('extra_hidden_file',False); p.unlink()
        wrong=args.copy(); wrong[5]='0'*64; check('wrong_external_manifest_anchor',False,wrong)
        check('restored',True); assert snap(copy)==before
    assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in PROTECTED.items())
    dirs=sum(e['kind']=='directory' for e in before.values()); assert dirs==20
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':4,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Six complete disposable-copy controls;child six selected-prose controls remain separate. Artifact evidence only.'})
    dump('input-authentication.json',{'source_blobs':11,'primary_incoming':7,'selected_or_derived_members':13,'tar_members_bound_in_memory':8,'historical_failures':failures,'stable_named_originals':22,'mutable_journal':1,'retained_original_copies':0,'limits':'Local canonical byte binding,not fresh protected-body semantic/remote identity/visual reading. PDF extract/render byte-bound only.'})
    dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':57,'whole_root_files':60,'subdirectories':dirs,'source_blobs':11,'primary_incoming':7,'selected_or_derived_members':13,'stable_named_originals':stable,'mutable_journal_observations':mutable,'artifact_cases':6,'negative_cases':4,'whole_actual_root_unchanged':True,'limits':'Artifact archive only,no mathematical or contribution gate or numerical suite. Verifier excludes modes/emptydirs/hardlinkpolicy;parent snapshots include current modes/links but exclude rootmode.'})
    print(json.dumps({'files':60,'subdirectories':dirs,'source_blobs':11,'primary_incoming':7,'selected_or_derived_members':13,'stable_originals':22,'cases':6}))

if __name__=='__main__': main()
