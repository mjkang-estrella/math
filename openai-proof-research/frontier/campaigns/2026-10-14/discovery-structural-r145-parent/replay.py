#!/usr/bin/env python3
"""Parent artifact intake and one exact finite witness, not a universal math gate."""
import datetime,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
from collections import Counter,defaultdict
from fractions import Fraction
from pathlib import Path
OUT=Path(__file__).resolve().parent;BASE=OUT.parent;PROJECT=BASE.parents[2];ROOT=BASE/'fresh-structural-discovery-r145'
spec=importlib.util.spec_from_file_location('archive_helpers',BASE/'discovery-arithmetic-r110-parent/replay.py');helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
sha,snap,PROTECTED=helper.sha,helper.snap,helper.PROTECTED
ANCHORS={'FINAL.md':'e307bdb9ebb27999b6b37462779e72293d02b427dbb84dffcdbd38065c8d5a78','MANIFEST.json':'b874cf794f76909e438f5c5a41f20dd498b6ac5e92597c3a94a45820904190bf','REPORT.md':'2d87f7fd97057c9ff97d89c9ddb2ed88833f3cb675b3531d8097a64c7f2b016b'}
def dump(n,d):(OUT/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
    assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=PROJECT)
    assert all(sha(PROJECT/p)==h for p,h in PROTECTED.items())
    now=datetime.datetime.now(datetime.timezone.utc).isoformat()
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=PROJECT,text=True).strip(),'initial_index_empty':True,'task_count':488,'task_index':485,'protected_unrelated_sha256':PROTECTED})
    before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current whole root only, not historical whole-parent or OS evidence.'})
    assert all(sha(ROOT/p)==h for p,h in ANCHORS.items())
    m=json.loads((ROOT/'MANIFEST.json').read_text());assert m['format']=='r145-exact-membership-v1' and len(m['files'])==63 and len(m['directories'])==34
    assert {p for p,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS)
    assert {p for p,e in before.items() if e['kind']=='directory'}==set(m['directories'])
    for p,e in m['files'].items():assert sha(ROOT/p)==e['sha256'] and (ROOT/p).stat().st_size==e['size']
    treefile=PROJECT/'sources/preprints-tree.json';assert sha(treefile)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree=json.loads(treefile.read_text());assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
    sources=json.loads((ROOT/'private/pinned/receipts.json').read_text());assert len(sources)==7
    for e in sources:
        data=(ROOT/e['local']).read_bytes();node=entries[e['canonical_path']]
        assert len(data)==e['size']==node['size'] and sha(ROOT/e['local'])==e['sha256']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha']
        assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
    primary=json.loads((ROOT/'private/primary/receipts.json').read_text());assert len(primary)==7
    for e in primary:
        p=ROOT/'private/primary'/(e['name']+'.pdf');assert sha(p)==e['sha256'] and p.stat().st_size==e['size']
        text='private/primary/'+e['name']+'.txt';assert sha(ROOT/text)==m['files'][text]['sha256']
    context=json.loads((ROOT/'private/context/receipts.json').read_text())['records'];assert len(context)==16
    stable=[];mutable=[]
    for e in context:
        assert sha(ROOT/e['snapshot'])==e['sha256'] and (ROOT/e['snapshot']).stat().st_size==e['bytes']
        current=sha(PROJECT/e['canonical_local_path'])
        if e['canonical_local_path']=='frontier/NEW-TEN-2026-10-14.md':mutable.append({'path':e['canonical_local_path'],'late_snapshot_sha256':e['sha256'],'current_sha256':current,'matches_late_snapshot_now':current==e['sha256'],'not_stability_input':True})
        else:assert current==e['sha256'];stable.append(e)
    assert len(stable)==15 and len(mutable)==1
    family=[0,7,11,13,15];assert all(a|b in family for a in family for b in family)
    iid=Counter(a|b for a in family for b in family);groups=defaultdict(list)
    for a in family:groups[a&1].append(a)
    prefix=defaultdict(Fraction)
    for group in groups.values():
        for a in group:
            for b in group:prefix[a|b]+=Fraction(1,len(family)*len(group))
    p=[int(Fraction(iid[a],25)*100) for a in family];q=[int(prefix[a]*100) for a in family]
    assert p==[4,12,12,12,60] and q==[20,5,5,5,65]
    numerator=1;denominator=1
    for x in p:numerator*=x**x
    for x in q:denominator*=x**x
    certificate=json.loads((ROOT/'private/prefix-exact-certificate.json').read_text())
    assert numerator==int(certificate['exp100_entropy_difference_numerator']) and denominator==int(certificate['denominator']) and numerator<denominator
    witness={'family_masks':family,'prefix_mask':1,'iid_numerators_over100':p,'prefix_numerators_over100':q,'exp100_entropy_difference_numerator':str(numerator),'denominator':str(denominator),'numerator_strictly_smaller':True,'meaning':'One exact same-prefix baseline-loss witness, maximum frequency4/5; no low-frequency counterexample or universal gate. Full4943-family census and floating scaling not rerun.'}
    cases=[]
    with tempfile.TemporaryDirectory(prefix='structural145-copy-',dir=OUT) as temp:
        copy=Path(temp)/'packet';shutil.copytree(ROOT,copy)
        args=[str(copy),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']]
        def check(label,expected,custom=None):
            state=snap(copy);r=subprocess.run([sys.executable,'-B',str(copy/'code/verify_packet.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
            assert (r.returncode==0)==expected,(label,r.stdout,r.stderr)
            assert snap(copy)==state
            cases.append({'case':label,'expected_pass':expected,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
        check('baseline_full_packet',True)
        p=copy/'notes/02-integrated-reduction-and-gap.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('modified_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data)
        p=copy/'private/.extra';p.write_text('extra');check('extra_hidden_payload',False);p.unlink()
        p=copy/'private/extra-empty-directory';p.mkdir();check('extra_empty_directory',False);p.rmdir()
        wrong=args.copy();wrong[4]='0'*64;check('wrong_external_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
    assert snap(ROOT)==before and all(sha(PROJECT/e['canonical_local_path'])==e['sha256'] for e in stable)
    assert all(sha(PROJECT/p)==h for p,h in PROTECTED.items())
    dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':5,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Complete copied packet byte controls, not universal mathematical gates.'})
    dump('prefix-diagnostic-replay.json',witness)
    dump('input-authentication.json',{'source_blobs':7,'primary_versions':primary,'primary_manifest_bound_texts':7,'stable_named_originals':stable,'mutable_context':mutable,'limits':'PDF receipts/text-manifest binding, not fresh extraction or primary-body reading. Current selected bytes, not first-read/whole-parent or journal stability.'})
    dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'verifier_sha256':sha(ROOT/'code/verify_packet.py'),'payload_files':63,'whole_root_files':66,'directories':34,'source_blobs':7,'primary_pdf_versions':7,'primary_manifest_bound_texts':7,'stable_named_originals':stable,'mutable_context':mutable,'artifact_cases':7,'negative_cases':5,'exact_prefix_witness_checked':True,'full_census_or_floating_scaling_rerun':False,'whole_actual_root_unchanged':True,'stable_originals_unchanged':True,'limits':'Artifact byte evidence plus one bounded exact witness. No full entropy-gain proof, independent mathematical/contribution gate, fresh source/primary/history body reading or historical whole-parent/OS certificate.'})
    print(json.dumps({'payloads':63,'whole_files':66,'source_blobs':7,'primary_versions':7,'stable_originals':15,'mutable_journal':1,'artifact_cases':7,'negative_cases':5,'exact_witness':True,'whole_root_unchanged':True}))
if __name__=='__main__':main()
