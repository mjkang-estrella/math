#!/usr/bin/env python3
"""Parent archive evidence only; no independent mathematical gate."""
import datetime, hashlib, json, os, shutil, stat, subprocess, sys, tempfile
from pathlib import Path
OUT=Path(__file__).resolve().parent
BASE=OUT.parent
PROJECT=BASE.parents[2]
ROOT=BASE/'fresh-structural-discovery-r142'
ANCHORS={'MANIFEST.json':'e938ab3a1d6e93562f90da6e2df339c8883758adbd49b7b7a1dd3e50a37a18de',
         'FINAL.json':'d574afe19b42d1e2fc32ef6a2b7118cd606c797450fb2e41695ddefb73a13446',
         'outsideREPORT.md':'a5487793960427a9a91e5c208d28ed50856df42d7ea429b31682ee9e402ee679'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(n,d):(OUT/n).write_text(json.dumps(d,indent=2)+'\n')
def snap(root):
    result={}
    for b,ds,fs in os.walk(root,followlinks=False):
        for n in sorted(ds+fs):
            p=Path(b)/n;s=p.lstat();e={'mode':stat.S_IMODE(s.st_mode)}
            if p.is_symlink():e.update(kind='symlink',target=os.readlink(p))
            elif stat.S_ISDIR(s.st_mode):e.update(kind='directory')
            elif stat.S_ISREG(s.st_mode):e.update(kind='file',bytes=s.st_size,sha256=sha(p),nlink=s.st_nlink)
            else:raise AssertionError(p)
            result[p.relative_to(root).as_posix()]=e
    return result
def main():
    now=datetime.datetime.now(datetime.timezone.utc).isoformat()
    protected={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9',
               'frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
    assert all(sha(PROJECT/p)==h for p,h in protected.items())
    assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=PROJECT)
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=PROJECT,text=True).strip(),'initial_index_empty':True,'protected_unrelated_sha256':protected,'task_count':470,'task_index':467})
    before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current root after prose/code reading,before copied execution;not an initial or historical whole-parent state.'})
    assert all(sha(ROOT/n)==h for n,h in ANCHORS.items())
    final=json.loads((ROOT/'FINAL.json').read_text());assert sha(ROOT/final['verifier_path'])==final['verifier_sha256']
    manifest=json.loads((ROOT/'MANIFEST.json').read_text())
    for e in manifest['files']:
        p=ROOT/e['path'];assert p.is_file() and not p.is_symlink() and sha(p)==e['sha256'] and p.stat().st_size==e['bytes']
    tree=json.loads((PROJECT/'sources/preprints-tree.json').read_text());assert len(tree['tree'])==13223 and tree['truncated'] is False
    assert sha(PROJECT/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    idx={e['path']:e for e in tree['tree']};sources=json.loads((ROOT/'packet/private/upstream-acquisition.json').read_text())
    for e in sources:
        p=ROOT/'packet/private/upstream'/e['path'];b=p.read_bytes();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        assert len(b)==e['bytes']==idx[e['path']]['size'] and blob==e['git_blob']==idx[e['path']]['sha'] and sha(p)==e['sha256']
    primaries=[]
    for n in ['acquisition.json','acquisition-second.json','acquisition-third.json']:
        for e in json.loads((ROOT/'packet/private/primary'/n).read_text()):
            p=ROOT/'packet/private/primary'/(e['name']+'.pdf');assert p.stat().st_size==e['size'] and sha(p)==e['sha256'];primaries.append(e)
    originals=json.loads((ROOT/'packet/private/current-originals.json').read_text())['files']
    for e in originals:assert sha(PROJECT/e['path'])==e['sha256']==sha(ROOT/'packet/private/originals'/e['path'])
    args=['--manifest-sha256',ANCHORS['MANIFEST.json'],'--final-sha256',ANCHORS['FINAL.json'],'--report-sha256',ANCHORS['outsideREPORT.md']];controls=[]
    with tempfile.TemporaryDirectory(prefix='structural142-copy-',dir=OUT) as tmp:
        copy=Path(tmp)/'r142';shutil.copytree(ROOT,copy);verifier=copy/'packet/public/verify_packet.py'
        def check(name,expected,argv=None):
            observed=snap(copy);p=subprocess.run([sys.executable,'-B',str(verifier),str(copy),*(argv or args)],capture_output=True,text=True,timeout=30)
            assert (p.returncode==0)==expected,(name,p.stdout,p.stderr);assert snap(copy)==observed
            controls.append({'case':name,'expected_pass':expected,'returncode':p.returncode,'fixture_unchanged':True,'stdout':p.stdout.strip(),'stderr':p.stderr.strip()})
        check('baseline',True)
        p=copy/'packet/public/interval_betti.py';b=p.read_bytes();p.write_bytes(b+b'\n# mutation\n');check('payload_mutation',False);p.write_bytes(b)
        p=copy/'extra.txt';p.write_text('extra');check('extra_file',False);p.unlink()
        p=copy/'packet/public/interval_betti.py';b=p.read_bytes();p.unlink();check('missing_payload',False);p.write_bytes(b)
        wrong=args.copy();wrong[1]='0'*64;check('wrong_detached_anchor',False,wrong)
        check('restored_copy',True);assert snap(copy)==before
        p=subprocess.run([sys.executable,'-B',str(copy/'packet/public/check_interval_betti.py')],capture_output=True,text=True,timeout=90);assert p.returncode==0,(p.stdout,p.stderr)
        diagnostic=json.loads(p.stdout);assert diagnostic==json.loads((ROOT/'packet/private/rational-diagnostic.json').read_text());dump('copied-diagnostic.json',diagnostic)
    assert snap(ROOT)==before
    assert all(sha(PROJECT/e['path'])==e['sha256'] for e in originals)
    assert all(sha(PROJECT/p)==h for p,h in protected.items())
    dump('copied-controls.json',{'cases':controls,'negative_cases':4,'positive_cases':2,'actual_root_unchanged':True,'copied_work_removed':True,'limits':'Per-call whole-copy identity observed separately;not a mathematical or OS enforcement gate.'})
    dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'payload_files':108,'whole_root_files':sum(e['kind']=='file' for e in before.values()),'pinned_source_blobs':25,'primary_pdf_receipts':primaries,'late_named_originals':originals,'artifact_cases':6,'negative_cases':4,'rational_Koszul_cases':diagnostic['checks'],'actual_root_unchanged':True,'current_named_originals_unchanged':True,'protected_unrelated_unchanged':True,'nominee':None,'count_change':0,
         'limits':'Artifact and finite support only. Verifier covers file membership/bytes/sizes/symlinks and envelope linkage,not modes,empty directories,hardlinks,current originals or canonical source blobs;parent snapshots and named checks are separate current observations. Private body authentication is not fresh parent semantic reading. Earlier modular/timed enumerations are not exhaustive rational validation. No priority/exclusion/historical whole-parent/OS enforcement gate.'})
    print(json.dumps({'payload_files':108,'source_blobs':25,'primary_pdfs':len(primaries),'late_named_originals':len(originals),'artifact_cases':6,'negative':4,'rational_cases':diagnostic['checks'],'root_and_originals_unchanged':True}))
if __name__=='__main__':main()
