#!/usr/bin/env python3
"""External-anchor adoption of T164F99's contribution review; no correctness gate."""
import hashlib,json,os,shutil,stat,subprocess,sys,tempfile
from pathlib import Path
FINAL='53f581b795963e6c8290b0286e47244faec5aedb3fd1c90b1faf90336489f31d'
MANIFEST='b34cd9b865124317b73ceaf5b4f8e82fa778c6f83afa3b6ce05de2bf14917fe2'
REPORT='cd7054e9a9c0e2d67fda07fca0b2708bba401daae924b5b1535e563f818e26da'
REVIEW='1d2f37422eabab1e0d47c83c42fd4a7caaa3c3afd11565ee0c6a20eb44d93e5b'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        s=p.lstat();v=[s.st_mode,s.st_nlink]
        if stat.S_ISREG(s.st_mode):v += [s.st_size,sha(p)]
        elif stat.S_ISLNK(s.st_mode):v += [os.readlink(p)]
        out[p.relative_to(root).as_posix()]=v
    return out
def run(args):
    r=subprocess.run([sys.executable,'-B',*map(str,args)],text=True,capture_output=True,
                     env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
    return {'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr}
def parent_verify(root,final=FINAL):
    # Author verifier accepts local sidecars rather than explicit external hashes.
    # Bind the task-handoff anchors here before invoking that unchanged verifier.
    for rel,h in [('FINAL.json',final),('packet/MANIFEST.json',MANIFEST),('REPORT.md',REPORT)]:
        if sha(root/rel)!=h:return {'exit':1,'stdout':'','stderr':'PARENT_EXTERNAL_ANCHOR_MISMATCH '+rel}
    manifest=json.loads((root/'packet/MANIFEST.json').read_text())['files']
    actual={p.relative_to(root/'packet').as_posix() for p in (root/'packet').rglob('*') if p.is_file() and p!=root/'packet/MANIFEST.json'}
    if actual!=set(manifest):return {'exit':1,'stdout':'','stderr':'PARENT_EXACT_FILE_SET_MISMATCH'}
    return run([root/'packet/public/verify.py','--root',root])
def main():
    parent=Path(__file__).resolve().parent;campaign=parent.parents[1];project=campaign.parents[2]
    review=campaign/'t164f99-contribution-r1';author=campaign/'fresh-arithmetic-discovery-r99'
    anchors={'FINAL.json':FINAL,'packet/MANIFEST.json':MANIFEST,'REPORT.md':REPORT,
             'packet/public/review.md':REVIEW,'packet/public/reading-limits.md':'54ca7df1c56e8be5f5986358e05e4015b9ddca2652c84b213d3dfefa68bfdddb'}
    for rel,h in anchors.items():assert sha(review/rel)==h,rel
    before_review=snapshot(review);before_author=snapshot(author)
    copies={
      'context/AGENTS.md':'AGENTS.md',
      'context/research-brief-2026-10-20.txt':'frontier/campaigns/2026-10-14/expanded-target-2026-10-17/research-brief-2026-10-20.txt',
      'context/contribution-r1-brief.txt':'frontier/campaigns/2026-10-14/discovery-arithmetic-r99-parent/contribution-r1-brief.txt',
      'context/upstream.json':'sources/upstream.json',
      'history/01-structural-r35-mixed164.md':'frontier/campaigns/2026-10-14/fresh-structural-discovery-r35/mixed164.md',
      'history/02-arithmetic-r94-other-screens.md':'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r94/packet/public/other-screens.md',
      'history/03-structural-r130-other-screens.md':'frontier/campaigns/2026-10-14/fresh-structural-discovery-r130/packet/public/other-screens.md',
      'history/04-structural-r130-report.md':'frontier/campaigns/2026-10-14/fresh-structural-discovery-r130/packet/public/report.md',
      'history/05-arithmetic-r1-candidate.md':'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r1/candidate.md',
      'history/06-r99-parent-assessment.md':'frontier/campaigns/2026-10-14/discovery-arithmetic-r99-parent/assessment.md',
      'history/07-r99-parent-intake.json':'frontier/campaigns/2026-10-14/discovery-arithmetic-r99-parent/intake.json'}
    bindings=[{'copy':'packet/private/'+rel,'origin':origin,'sha256':sha(project/origin),
               'match':sha(review/'packet/private'/rel)==sha(project/origin)} for rel,origin in copies.items()]
    assert all(r['match'] for r in bindings)
    external={r['origin']:r['sha256'] for r in bindings};external['sources/preprints-tree.json']=sha(project/'sources/preprints-tree.json')
    assert external['sources/preprints-tree.json']==TREE
    tree={e['path']:e for e in json.loads((project/'sources/preprints-tree.json').read_text())['tree']}
    canonical=[];prefix='preprints/Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026/'
    for p in sorted((review/'packet/private/source').iterdir()):
        if p.name.startswith('build_sections_'):rel='build/sections/'+p.name[len('build_sections_'):]
        elif p.name.startswith('build_'):rel='build/'+p.name[len('build_'):]
        else:rel=p.name
        path=prefix+rel;e=tree[path];data=p.read_bytes()
        assert e['type']=='blob' and len(data)==e['size']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['sha']
        canonical.append({'path':path,'git_blob':e['sha'],'sha256':sha(p),
                          'canonical_url':'https://raw.githubusercontent.com/openai/math/'+PIN+'/'+path})
    direct=parent_verify(review)
    with tempfile.TemporaryDirectory(prefix='copied-review-',dir=parent) as td:
        copy=Path(td)/'review';copy.mkdir();shutil.copytree(review/'packet',copy/'packet',symlinks=True)
        for f in ['FINAL.json','FINAL.sha256','REPORT.md','REPORT.sha256']:shutil.copy2(review/f,copy/f)
        clean=parent_verify(copy);snap=snapshot(copy);wrong=parent_verify(copy,'0'*64)
        wrong_unchanged=snap==snapshot(copy)
        controls=run([copy/'packet/public/controls.py'])
        receipt=json.loads((copy/'artifact-controls.json').read_text())
    unchanged_review=before_review==snapshot(review);unchanged_author=before_author==snapshot(author)
    unchanged_external=external=={rel:sha(project/rel) for rel in external}
    ok=(direct['exit']==0 and clean['exit']==0 and wrong['exit']!=0 and wrong_unchanged
        and controls['exit']==0 and receipt['all_as_expected'] and unchanged_review and unchanged_author and unchanged_external)
    out={'kind':'PARENT_CONTRIBUTION_ARTIFACT_ADOPTION','mathematical_gate':False,'detached_anchors':anchors,
         'original_verify_with_parent_anchor_wrapper':direct,'copy_verify':clean,'wrong_external_final':wrong,
         'wrong_external_final_copy_unchanged':wrong_unchanged,'copied_controls':controls,'copied_control_receipt':receipt,
         'canonical_sources':canonical,'current_project_bindings':bindings,'external_originals':external,
         'whole_review_root_unchanged':unchanged_review,'whole_author_root_unchanged':unchanged_author,
         'external_originals_unchanged':unchanged_external,'all_expected':ok,
         'coverage_limits':'Original verifier uses local sidecars and excludes pycache; parent wrapper binds external handoff hashes and checks all actual packet files. Directory inventory, modes, hardlinks and syscall denial are not sealed by that verifier. Parent preservation snapshots include modes/link counts. Copied controls total8:clean plus7 mutations. Sources authenticate canonically from flattened filenames; no acquisition register is invented.'}
    (parent/'replay.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'all_expected':ok,'copied_cases':len(receipt['cases']),'sources':len(canonical),
                      'history_context_bindings':len(bindings),'external_originals':len(external),
                      'author_unchanged':unchanged_author,'review_unchanged':unchanged_review}))
    return 0 if ok else 1
if __name__=='__main__':sys.exit(main())
