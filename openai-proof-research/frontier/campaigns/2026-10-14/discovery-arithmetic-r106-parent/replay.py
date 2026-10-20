#!/usr/bin/env python3
"""Parent artifact/finite-support intake, never an independent mathematical gate."""
import datetime, hashlib, json, os, shutil, stat, subprocess, sys, tempfile
from pathlib import Path
OUT=Path(__file__).resolve().parent
BASE=OUT.parent
PROJECT=BASE.parents[2]
ROOT=BASE/'fresh-arithmetic-discovery-r106'
ANCHORS={'final':'9fd7f968275e961643adb4cb594eb9f37ce6be25ff1b4d5c903f24b023be97c7',
         'manifest':'0f38e5f3e9f6de508134d6d0a85d1fbe097983f3a2a5ac5db83fb0cf6d7adf9e',
         'report':'32b24bf9a9103dca5050f6631aa35810878302297f66cf98f6d441a97c39604c'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(n,d):(OUT/n).write_text(json.dumps(d,indent=2)+'\n')
def snap(root):
    result={}
    for b,ds,fs in os.walk(root,followlinks=False):
        for n in sorted(ds+fs):
            p=Path(b)/n;s=p.lstat();row={'mode':stat.S_IMODE(s.st_mode)}
            if p.is_symlink():row.update(kind='symlink',target=os.readlink(p))
            elif stat.S_ISDIR(s.st_mode):row.update(kind='directory')
            elif stat.S_ISREG(s.st_mode):row.update(kind='file',bytes=s.st_size,sha256=sha(p),nlink=s.st_nlink)
            else:raise AssertionError(p)
            result[p.relative_to(root).as_posix()]=row
    return result
def main():
    now=datetime.datetime.now(datetime.timezone.utc).isoformat()
    protected={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9',
               'frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
    assert all(sha(PROJECT/p)==h for p,h in protected.items())
    assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=PROJECT)
    dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=PROJECT,text=True).strip(),
         'initial_index_empty':True,'protected_unrelated_sha256':protected,'task_count':469,'task_index':466})
    before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current full root after public prose/code reads,before copied execution;no historical whole-parent preservation.'})
    for k,p in [('final',ROOT/'packet/FINAL.json'),('manifest',ROOT/'packet/MANIFEST.json'),('report',ROOT/'REPORT.md')]:assert sha(p)==ANCHORS[k]
    manifest=json.loads((ROOT/'packet/MANIFEST.json').read_text())
    for n,e in manifest['files'].items():
        rel=Path(n);assert not rel.is_absolute() and '..' not in rel.parts
        p=ROOT/'packet'/n;assert p.is_file() and not p.is_symlink() and p.stat().st_size==e['size'] and sha(p)==e['sha256']
    bindings=json.loads((ROOT/'packet/private/original-bindings.json').read_text());compared=[]
    for e in bindings:
        assert sha(PROJECT/e['original'])==e['sha256']
        compared.append({'original':e['original'],'sha256':e['sha256'],'mutable_observation':e['mutable'],'captured':e['captured']})
    args=sum([['--'+k+'-sha256',v] for k,v in ANCHORS.items()],[])+['--original-project',str(PROJECT)]
    def run(argv):
        p=subprocess.run(argv,capture_output=True,text=True,timeout=90);assert p.returncode==0,(p.stdout,p.stderr);return json.loads(p.stdout)
    with tempfile.TemporaryDirectory(prefix='arithmetic106-copy-',dir=OUT) as tmp:
        copy=Path(tmp)/ROOT.name;copy.mkdir();shutil.copytree(ROOT/'packet',copy/'packet');shutil.copy2(ROOT/'REPORT.md',copy/'REPORT.md')
        artifact=run([sys.executable,'-B',str(copy/'packet/public/verify.py'),'--root',str(copy),*args])
        run([sys.executable,'-B',str(copy/'packet/public/controls.py'),'--root',str(copy),*args])
        controls=json.loads((copy/'work/controls-results.json').read_text());assert len(controls['cases'])==9 and all(e['accepted']==e['expected'] and e['fixture_unchanged_by_verifier'] for e in controls['cases'])
        diagnostic=run([sys.executable,'-B',str(copy/'packet/public/diagnostic.py')]);assert diagnostic==json.loads((ROOT/'packet/private/diagnostic-result.json').read_text())
        dump('copied-controls.json',controls);dump('copied-diagnostic.json',diagnostic)
    assert snap(ROOT)==before
    assert all(sha(PROJECT/e['original'])==e['sha256'] for e in bindings)
    assert all(sha(PROJECT/p)==h for p,h in protected.items())
    dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'artifact_result':artifact,'copied_artifact_cases':9,'negative_cases':7,'finite_centralizer_cases':8,'diagnostic_matches_sealed_result':True,
         'named_original_comparisons':compared,'whole_actual_root_unchanged':True,'current_named_originals_unchanged':True,'protected_unrelated_unchanged':True,'nominee':None,'count_change':0,
         'limits':'Artifact/finite support only. Verifier checks70payloads plus2sealfiles,13directory modes,single-link regular payloads,22pinnedblobs,3PDFreceipts and21currentoriginals. Parent private-body hashes are not semantic rereads. Nineteen stable inputs/two mutable observations are late captures. Child controls assert per-call regular-file bytes only,not per-call modes/dirs/links;parent whole-root snapshot is separate. Tensor diagnostic is split,not a division witness. No priority/exclusion/historical whole-parent or OS enforcement gate.'})
    print(json.dumps({'artifact':artifact,'cases':9,'negative':7,'finite_cases':8,'root_and_named_originals_unchanged':True}))
if __name__=='__main__':main()
