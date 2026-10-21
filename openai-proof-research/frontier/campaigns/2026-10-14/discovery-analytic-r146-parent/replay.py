#!/usr/bin/env python3
"""Completed analytic146 byte archive; no analytic or contribution gate."""
import datetime, gzip, hashlib, importlib.util, io, json, shutil, subprocess, sys, tarfile, tempfile
from pathlib import Path

O=Path(__file__).resolve().parent; B=O.parent; P=B.parents[2]; ROOT=B/'fresh-analytic-discovery-r146'
spec=importlib.util.spec_from_file_location('archive_helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py')
h=importlib.util.module_from_spec(spec); spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'3a7a06c4d9901ae2c3ccbdd9fe646ccadf31cafc9f530e15cdf2821d47ff1250','MANIFEST.json':'87d1de2b49e524830b912766601ff8a97ddbdd2ad3057f3362a6c4e436b4d6a0','REPORT.md':'f2d4f8b4f4dca30c7997e4be6beedc74cbc94c46be8756a33b22d9d71e4ba083'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p): return json.loads(p.read_text())
def dump(n,d): (O/n).write_text(json.dumps(d,indent=2)+'\n')
def digest(b): return hashlib.sha256(b).hexdigest()

def main():
    now=datetime.datetime.now(datetime.timezone.utc).isoformat()
    assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P)
    assert len(read(B/'tasks.json')['tasks'])==512
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'initial_index_empty':True,'task_count':512,'task_index':509,'protected_unrelated_sha256':PROTECTED})
    before=snap(ROOT)
    dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current completed whole root,root-directory mode excluded;no historical whole-project or OS certificate.'})
    st=read(O/'task-status.json')['structuredContent']
    assert st['status']=='completed' and not st['hasPendingChildRuns'] and all(v in st['summary'] for v in ANCHORS.values())
    assert all(sha(ROOT/n)==v for n,v in ANCHORS.items())
    m=read(ROOT/'MANIFEST.json'); assert m['schema']=='r146-exact-payload-v1' and len(m['files'])==66
    assert {p for p,e in before.items() if e['kind']=='file'}=={e['path'] for e in m['files']}|set(ANCHORS)
    for e in m['files']: assert (ROOT/e['path']).stat().st_size==e['size'] and sha(ROOT/e['path'])==e['sha256']
    tp=P/'sources/preprints-tree.json'
    assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree=read(tp); assert len(tree['tree'])==13223 and not tree['truncated']; entries={e['path']:e for e in tree['tree']}
    auth=read(ROOT/'SOURCE-AUTH.json');source=auth['entries'];assert len(source)==11 and auth['tree_sha256']==sha(tp) and auth['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
    prefix='preprints/Stable-Self-Similar-Blowup-for-a-Supercritical-Defocusing-Schrodinger-Equation-on-the-Torus-September-24-2026/'
    assert {e['canonical_path'] for e in source}=={p for p,e in entries.items() if p.startswith(prefix) and e['type']=='blob' and not p.endswith('.pdf') and '/verification/' not in p}
    for e in source:
        data=(ROOT/e['selected_path']).read_bytes();node=entries[e['canonical_path']]
        assert len(data)==e['size']==node['size'] and digest(data)==e['sha256']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['gitblob_sha1']==node['sha']
        assert e['url']=='https://raw.githubusercontent.com/openai/math/'+auth['pin']+'/'+e['canonical_path']
    primary=read(ROOT/'PRIMARY-AUTH.json');assert len(primary)==4;members=0
    for e in primary:
        p=ROOT/'private/primary'/e['id'];data=(p/'incoming.bin').read_bytes()
        assert len(data)==e['size'] and digest(data)==e['sha256'] and e['url']=='https://arxiv.org/src/'+e['id']
        with tarfile.open(fileobj=io.BytesIO(data),mode='r:*') as archive:
            for row in e['selected']:
                node=archive.getmember(row['member']);assert node.isfile();d=archive.extractfile(node).read()
                assert d==(p/'selected'/row['member']).read_bytes() and len(d)==row['size'] and digest(d)==row['sha256'];members+=1
        assert {f.relative_to(p/'selected').as_posix() for f in (p/'selected').rglob('*') if f.is_file()}=={e['member'] for e in e['selected']}
    assert members==8
    originals=read(ROOT/'ORIGINALS-AUTH.json')['entries'];assert len(originals)==13;stable=[]
    for e in originals:
        q=ROOT/e['selected_path'];p=P/e['original_path'];assert p.read_bytes()==q.read_bytes() and p.stat().st_size==e['size'] and sha(p)==e['sha256']
        stable.append({'path':e['original_path'],'sha256':e['sha256'],'bytes':e['size'],'limit':'Late current whole-original/copy equality,not first-read/inherited-archive certification or fresh semantic reading.'})
    recheck=read(ROOT/'AUTH-CHECK.json');assert [recheck[k] for k in ['tree_entries','canonical_source_bodies','incoming_primary_archives','selected_members','late_original_identities']]==[13223,11,4,8,13] and recheck['all_matched']
    ctl=read(ROOT/'CONTROL-RESULTS.json');fixture=ROOT/'private/control-fixture';fm=read(fixture/'MANIFEST.json')
    assert len(ctl['results'])==6 and len(fm['files'])==1 and ctl['independent_selected_manifest']
    assert (fixture/'sample.md').read_bytes()==(ROOT/'GAPS.md').read_bytes() and sha(ROOT/'GAPS.md')==ctl['selection']['sha256']
    assert fm['files'][0]['path']=='sample.md' and fm['files'][0]['sha256']==ctl['selection']['sha256']
    for n,v in ctl['anchors'].items():assert sha(fixture/n)==v
    assert all((e['returncode']==0)==e['expected_accept'] and e['before']==e['after'] for e in ctl['results'])
    cases=[]
    with tempfile.TemporaryDirectory(prefix='analytic146-copy-',dir=O) as temp:
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
    dirs=sum(e['kind']=='directory' for e in before.values()); assert dirs==17
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':4,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Six complete disposable-copy controls;child six selected-prose controls remain separate. Artifact evidence only.'})
    dump('input-authentication.json',{'source_blobs':11,'primary_incoming_archives':4,'selected_members_bound_in_memory':8,'stable_whole_original_copies':13,'limits':'Canonical local bytes and retained-copy binding only,no fresh network/protected-body semantic reading or inherited whole-archive certificate.'})
    dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':66,'whole_root_files':69,'subdirectories':dirs,'source_blobs':11,'primary_incoming_archives':4,'selected_members':8,'stable_named_originals':stable,'artifact_cases':6,'negative_cases':4,'whole_actual_root_unchanged':True,'limits':'Artifact archive only,no PDE/formal/numerical mathematical suite or independent grade.Verifier excludes modes/emptydirs/hardlinkpolicy,parent snapshot excludes rootmode.'})
    print(json.dumps({'files':69,'subdirectories':dirs,'source_blobs':11,'primary_archives':4,'selected_members':8,'stable_copies':13,'cases':6}))

if __name__=='__main__': main()
