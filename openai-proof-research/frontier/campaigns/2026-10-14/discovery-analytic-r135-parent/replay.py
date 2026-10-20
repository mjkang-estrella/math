#!/usr/bin/env python3
"""Parent artifact intake only; no independent mathematical verdict."""
import datetime, hashlib, json, os, shutil, stat, subprocess, sys, tempfile
from pathlib import Path
OUT=Path(__file__).resolve().parent
BASE=OUT.parent
PROJECT=BASE.parents[2]
ROOT=BASE/'fresh-analytic-discovery-r135'
ANCHORS={'manifest':'b879e1834bb52613cb96fe2c1b9bbe94d1f1fc248278600353e02f65fe621cd3',
         'final':'3904ce18a96b3ee465f482482666fc47d1d6ff43a4383a27f6741d00805a1606',
         'report':'eb201d80ac8fd790ed80e42eb2fb18a6b53401a9fa014bb0b3ccfe26cf9fb501'}
SCOPE='cc80f307514d0fe7ab47079b6cda7d47abb7ce4c80aa616d0ebc02cc1b96e939'
PROOF='b3159d956644b4fd5befcf55de5a965eb91278798f6b8f57f713a84aab0d2172'
VERIFIER='8909b476e677e0eaf2bd72896cadf8c7424f47d0c7f90ffb053ecac2a0104551'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(n,d):(OUT/n).write_text(json.dumps(d,indent=2)+'\n')
def snap(root):
    out={}
    for b,ds,fs in os.walk(root,followlinks=False):
        for n in sorted(ds+fs):
            p=Path(b)/n;s=p.lstat();row={'mode':stat.S_IMODE(s.st_mode)}
            if stat.S_ISDIR(s.st_mode):row.update(kind='directory')
            elif stat.S_ISREG(s.st_mode):row.update(kind='file',bytes=s.st_size,sha256=sha(p),nlink=s.st_nlink)
            else:raise AssertionError(p)
            out[p.relative_to(root).as_posix()]=row
    return out
def main():
    now=datetime.datetime.now(datetime.timezone.utc).isoformat()
    protected={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9',
               'frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
    assert all(sha(PROJECT/p)==h for p,h in protected.items())
    assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=PROJECT)
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=PROJECT,text=True).strip(),
         'initial_index_empty':True,'protected_unrelated_sha256':protected,'task_count':468,'task_index':464})
    before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current observation after prose/code/source-interface reads,before copied execution. No historical whole-parent preservation.'})
    for k,p in [('manifest',ROOT/'packet/MANIFEST.json'),('final',ROOT/'FINAL.md'),('report',ROOT/'REPORT.md')]:assert sha(p)==ANCHORS[k]
    assert sha(ROOT/'packet/public/verify_packet.py')==VERIFIER
    assert sha(ROOT/'packet/public/FROZEN-SCOPE.md')==SCOPE and sha(ROOT/'packet/public/author-proof.md')==PROOF
    final=(ROOT/'FINAL.md').read_text();assert all(h in final for h in [ANCHORS['manifest'],ANCHORS['report'],VERIFIER,SCOPE])
    local=json.loads((ROOT/'ANCHORS.json').read_text());assert all(local[k]==v for k,v in ANCHORS.items())
    manifest=json.loads((ROOT/'packet/MANIFEST.json').read_text())
    for e in manifest['files']:
        p=ROOT/'packet'/e['path'];assert p.is_file() and not p.is_symlink() and p.stat().st_size==e['size'] and sha(p)==e['sha256']
    tree=json.loads((PROJECT/'sources/preprints-tree.json').read_text());assert len(tree['tree'])==13223 and tree['truncated'] is False
    assert sha(PROJECT/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    bypath={e['path']:e for e in tree['tree']};sources=[]
    for name in ['A-counterexample-to-the-Monge-ansatz-acquisitions.json','Sharp-One-Third-acquisitions.json']:
        for e in json.loads((ROOT/'packet/private'/name).read_text()):
            p=ROOT/'packet/private/upstream'/e['path'];b=p.read_bytes();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
            assert len(b)==e['size']==bypath[e['path']]['size'] and blob==e['git_blob']==bypath[e['path']]['sha'] and sha(p)==e['sha256']
            sources.append({'path':e['path'],'sha256':e['sha256'],'git_blob':blob})
    primary=[]
    for name in ['acquisitions.json','late-acquisitions.json','parametrix-acquisition.json','dgw-acquisition.json']:
        obj=json.loads((ROOT/'packet/private/primary'/name).read_text());records=obj if isinstance(obj,list) else [dict(obj,name='parametrix' if name.startswith('parametrix') else 'djellout-guillin-wu-v1')]
        for e in records:
            p=ROOT/'packet/private/primary'/(e['name']+'.pdf');assert p.stat().st_size==e['size'] and sha(p)==e['sha256']
            primary.append({'name':e['name'],'url':e['url'],'sha256':e['sha256']})
    bindings=[]
    for e in json.loads((ROOT/'packet/private/late-original-bindings.json').read_text())['files']:
        assert sha(ROOT/'packet'/e['copy'])==e['sha256'];current=sha(PROJECT/e['path']);mutable=e['path']=='frontier/NEW-TEN-2026-10-14.md'
        assert mutable or current==e['sha256'];bindings.append({'path':e['path'],'capture_sha256':e['sha256'],'current_sha256':current,'mutable_observation':mutable,'currently_matches':current==e['sha256']})
    def run(argv):
        p=subprocess.run(argv,capture_output=True,text=True,timeout=90);assert p.returncode==0,(p.stdout,p.stderr);return json.loads(p.stdout)
    with tempfile.TemporaryDirectory(prefix='analytic135-copy-',dir=OUT) as tmp:
        copied=Path(tmp)/ROOT.name;shutil.copytree(ROOT,copied)
        args=['--manifest-sha',ANCHORS['manifest'],'--final-sha',ANCHORS['final'],'--report-sha',ANCHORS['report']]
        artifact=run([sys.executable,'-B',str(copied/'packet/public/verify_packet.py'),str(copied),*args])
        run([sys.executable,'-B',str(copied/'packet/public/copied_artifact_controls.py')])
        controls=json.loads((copied/'copied-controls.json').read_text());assert len(controls['controls'])==9 and controls['all_expected_outcomes_observed']
        diagnostic=run([sys.executable,'-B',str(copied/'packet/public/normalization-check.py')]);assert diagnostic==json.loads((ROOT/'packet/private/normalization-check.json').read_text())
        dump('copied-controls.json',controls);dump('copied-diagnostic.json',diagnostic)
    assert snap(ROOT)==before
    assert all(sha(PROJECT/e['path'])==e['current_sha256'] for e in bindings)
    assert all(sha(PROJECT/p)==h for p,h in protected.items())
    dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'scope_sha256':SCOPE,'proof_sha256':PROOF,'FINAL_bound_verifier_sha256':VERIFIER,
         'artifact':artifact,'packet_files_excluding_manifest':82,'whole_root_files':sum(e['kind']=='file' for e in before.values()),'pinned_source_blobs':sources,'primary_pdf_receipts':primary,'late_input_comparisons':bindings,
         'copied_artifact_cases':9,'negative_cases':7,'finite_covariance_examples':3,'normalization_result_matches':True,'whole_actual_root_unchanged':True,'current_named_originals_unchanged':True,'protected_unrelated_unchanged':True,
         'limits':'Artifact/finite rational support only; no independent correctness or contribution. Twenty pinned blobs include nine abandoned Source374 files,not semantic reads. Fifteen selected originals are explicitly late captures,14stable and1mutable observation. Verifier covers regular-file membership/bytes,not modes/emptydirs/hardlinks/current originals/Git blobs;parent snapshots and input checks are separate. Controls run on a copy after external bootstrap;convenience ANCHORS is not an independent trust root. No per-case original preservation,OS enforcement,complete primary/history semantic reread or priority/exclusion certificate.'})
    print(json.dumps({'artifact_files':artifact['files_excluding_manifest'],'sources':len(sources),'primary_pdfs':len(primary),'late_bindings':len(bindings),'artifact_cases':9,'negative':7,'covariance_examples':3,'root_unchanged':True}))
if __name__=='__main__':main()
