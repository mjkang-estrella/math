#!/usr/bin/env python3
"""Read and replay authenticated arithmetic105 artifacts on a fresh copy only."""
import datetime, hashlib, json, os, shutil, stat, subprocess, sys, tempfile
from pathlib import Path

OUT=Path(__file__).resolve().parent
BASE=OUT.parent
PROJECT=BASE.parents[2]
ROOT=BASE/'fresh-arithmetic-discovery-r105'
ANCHORS={'final':'aeaaabb8d8efd774065ca9f53a6d966e26044f50bfc03824b2881c2752de4b92',
         'manifest':'56a312c05ee17b34a60e3b2bc6d4dbaa130ecd711bc503815641e5a5f64b6c72',
         'report':'decfe40c227c5b5a4868442f2af889c4971c89906cc92ac9b69e4daeb673dfc2'}

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(n,d):(OUT/n).write_text(json.dumps(d,indent=2)+'\n')
def snap(root):
    out={}
    for b,ds,fs in os.walk(root,followlinks=False):
        for n in sorted(ds+fs):
            p=Path(b)/n;s=p.lstat();row={'mode':stat.S_IMODE(s.st_mode)}
            if p.is_symlink():row.update(kind='symlink',target=os.readlink(p))
            elif stat.S_ISDIR(s.st_mode):row.update(kind='directory')
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
         'initial_index_empty':True,'protected_unrelated_sha256':protected,'task_count':466,'task_index':465})
    before=snap(ROOT)
    dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current interval after parent prose/code reading. Symlinks in old mutation fixtures are recorded without following. No historical whole-parent preservation.'})
    for k,p in [('final',ROOT/'packet/FINAL.json'),('manifest',ROOT/'packet/MANIFEST.json'),('report',ROOT/'REPORT.md')]:assert sha(p)==ANCHORS[k]
    manifest=json.loads((ROOT/'packet/MANIFEST.json').read_text())
    for n,row in manifest['files'].items():
        p=ROOT/'packet'/n;assert p.is_file() and not p.is_symlink()
        assert p.stat().st_size==row['size'] and sha(p)==row['sha256']
    # The executable verifier and diagnostics are payloads of this externally anchored manifest.
    bindings=json.loads((ROOT/'packet/private/context/bindings.json').read_text())
    compared=[]
    for b in bindings:
        p=PROJECT/b['original'];assert sha(p)==b['sha256']
        compared.append({'original':b['original'],'sha256':b['sha256'],'kind':b['kind'],'timing':b['timing']})
    args=sum([['--'+k+'-sha256',v] for k,v in ANCHORS.items()],[])
    def run(argv):
        r=subprocess.run(argv,capture_output=True,text=True,timeout=90)
        assert r.returncode==0,(r.stdout,r.stderr)
        return json.loads(r.stdout)
    with tempfile.TemporaryDirectory(prefix='arithmetic105-copy-',dir=OUT) as t:
        copied=Path(t)/ROOT.name;copied.mkdir()
        shutil.copytree(ROOT/'packet',copied/'packet');shutil.copy2(ROOT/'REPORT.md',copied/'REPORT.md')
        artifact=run([sys.executable,'-B',str(copied/'packet/public/verify.py'),'--root',str(copied),*args,'--original-project',str(PROJECT)])
        controls=run([sys.executable,'-B',str(copied/'packet/public/control_check.py'),'--root',str(copied),*args])
        assert len(controls['cases'])==9 and all(x['fixture_unchanged'] for x in controls['cases'])
        diagnostic=run([sys.executable,'-B',str(copied/'packet/public/representation_check.py')])
        assert diagnostic==json.loads((ROOT/'packet/public/diagnostic-results.json').read_text())
        dump('copied-controls.json',controls);dump('copied-diagnostic.json',diagnostic)
    assert snap(ROOT)==before
    assert all(sha(PROJECT/p)==h for p,h in protected.items())
    assert all(sha(PROJECT/b['original'])==b['sha256'] for b in bindings)
    dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,
         'artifact_result':artifact,'artifact_cases':9,'negative_cases':8,'diagnostic_matches_sealed_result':True,
         'whole_actual_root_unchanged':True,'named_original_comparisons':compared,'named_originals_unchanged':True,
         'protected_unrelated_unchanged':True,'nominee':None,'count_change':0,
         'limits':'Artifact and finite support only; no independent mathematical gate. Sixty-six payloads plus two seal files; directory/mode/single-link payload and canonical pinned checks are performed by the authenticated copied verifier. No parent semantic reread of private source/primary/history/search bodies, priority/exclusion clearance or OS enforcement. All copied work removed.'})
    print(json.dumps({'artifact':artifact,'cases':9,'negative':8,'diagnostic':'MATCH','whole_root_unchanged':True}))

if __name__=='__main__':main()
