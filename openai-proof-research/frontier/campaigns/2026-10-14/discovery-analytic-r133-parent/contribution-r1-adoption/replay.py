#!/usr/bin/env python3
"""Detached contribution-review adoption only; no correctness/acceptance gate."""
import hashlib,json,os,shutil,stat,subprocess,sys,tempfile
from pathlib import Path
FINAL='c84fa541285ee770acf37b9df9728dee603bb40202fec6dfc868173a6069e7c7'
MANIFEST='66405c96dd6b76d25e7a290dc8d17d1f24abf489bcb2c45fd7e4deb8eef13656'
REPORT='89595f993f3f5ec2aa98bc87cfa30eefdaa2d4319b5f77b3c45349191e72627b'
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
def run(args,cwd):
    r=subprocess.run([sys.executable,'-B',*map(str,args)],cwd=cwd,text=True,capture_output=True,
                     env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
    return {'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr}
def main():
    parent=Path(__file__).resolve().parent;campaign=parent.parents[1];project=campaign.parents[2]
    review=campaign/'t088p133-contribution-r1';author=campaign/'fresh-analytic-discovery-r133'
    for rel,h in [('FINAL.json',FINAL),('packet/MANIFEST.json',MANIFEST),('REPORT.md',REPORT)]:assert sha(review/rel)==h
    fin=json.loads((review/'FINAL.json').read_text());assert fin['review_manifest_sha256']==MANIFEST and fin['verdict']=='SUBSTANTIAL'
    before_author=snapshot(author);before_review=snapshot(review)
    inputs={}
    for name in ['input-hashes-start.txt','parent-late-additions.txt']:
        for line in (review/'work'/name).read_text().splitlines():
            if not line.strip():continue
            h,rel=line.split('  ',1);p=(campaign/rel).resolve();assert sha(p)==h,rel
            inputs[p.relative_to(project).as_posix()]=h
    assert sha(project/'sources/preprints-tree.json')==TREE
    td=json.loads((project/'sources/preprints-tree.json').read_text());assert td['truncated'] is False and len(td['tree'])==13223
    tree={r['path']:r for r in td['tree']}
    reg=json.loads((review/'work/acquisition-register.json').read_text())
    for r in reg['pinned_upstream']:
        data=(review/'private/upstream'/r['path']).read_bytes();e=tree[r['path']]
        assert r['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+r['path']
        assert len(data)==r['size']==r['tree_size']==e['size']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==r['git_blob']==r['tree_blob']==e['sha']
        assert hashlib.sha256(data).hexdigest()==r['sha256']
    for r in reg['independent_primary']:
        p=review/r['path'];assert p.stat().st_size==r['size'] and sha(p)==r['sha256'],r['path']
    common=['--root','.', '--manifest-sha256',MANIFEST,'--final-sha256',FINAL,'--report-sha256',REPORT]
    direct=run(['packet/public/verify.py',*common],review)
    with tempfile.TemporaryDirectory(prefix='copied-review-',dir=parent) as temp:
        copy=Path(temp)/'review';shutil.copytree(review,copy,symlinks=True,ignore=shutil.ignore_patterns('controls','scratch'))
        clean=run(['packet/public/verify.py',*common],copy)
        bad=list(common);bad[bad.index('--final-sha256')+1]='0'*64
        copy_before=snapshot(copy);wrong=run(['packet/public/verify.py',*bad],copy);wrong_unchanged=copy_before==snapshot(copy)
        anchors=Path(temp)/'anchors.json';anchors.write_text(json.dumps({'final':FINAL,'manifest':MANIFEST,'report':REPORT}))
        controls=run(['packet/public/controls.py','--root',copy,'--anchors',anchors,'--tmp',copy/'controls/review-controls'],copy)
        receipt=json.loads(controls['stdout'].rsplit('\nCONTROLS',1)[0].strip())
    author_unchanged=before_author==snapshot(author);review_unchanged=before_review==snapshot(review)
    originals_unchanged=inputs=={rel:sha(project/rel) for rel in inputs}
    ok=(direct['exit']==0 and clean['exit']==0 and wrong['exit']!=0 and wrong_unchanged
        and controls['exit']==0 and len(receipt)==8 and all(r['as_expected'] for r in receipt)
        and author_unchanged and review_unchanged and originals_unchanged)
    out={'kind':'PARENT_CONTRIBUTION_ARTIFACT_ADOPTION','mathematical_gate':False,
         'detached_anchors':{'final':FINAL,'manifest':MANIFEST,'report':REPORT},
         'manifest_payload_files':len(json.loads((review/'packet/MANIFEST.json').read_text())['files']),
         'review_sha256':sha(review/'packet/public/review.md'),'reading_limits_sha256':sha(review/'packet/public/reading-limits.md'),
         'original_verify':direct,'copy_verify':clean,'wrong_final':wrong,'wrong_final_copy_unchanged':wrong_unchanged,
         'copied_controls':controls,'copied_control_receipt':receipt,
         'canonical_pinned_preprint_bodies':len(reg['pinned_upstream']),
         'primary_acquisition_records':len(reg['independent_primary']),
         'primary_count_limit':'Fourteen acquisition records include derivatives, metadata and two Lean-doc revision checks, not fourteen papers; only13 preprint bodies authenticate against the complete preprints tree.',
         'external_original_hashes':inputs,'whole_author_root_unchanged':author_unchanged,
         'whole_review_root_unchanged':review_unchanged,'external_originals_unchanged':originals_unchanged,'all_expected':ok,
         'coverage_limits':'Original verifier authenticates bytes/file sets in packet,private,work and detached hashes; not exact directories,modes,hardlinks or syscall denial. Parent unchanged snapshots include modes/link counts. Original eight controls check expected exits, not per-copy preservation; separate parent wrong-anchor copy and actual original roots are preservation-checked. No portable release.'}
    (parent/'replay.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'all_expected':ok,'copied_cases':len(receipt),'sources':len(reg['pinned_upstream']),
                      'acquisition_records':len(reg['independent_primary']),'external_originals':len(inputs),
                      'author_unchanged':author_unchanged,'review_unchanged':review_unchanged}))
    return 0 if ok else 1
if __name__=='__main__':sys.exit(main())
