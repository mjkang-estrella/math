#!/usr/bin/env python3
"""MIT. Copied mutation tests. All writes stay under this review root.
--record stores a receipt; subsequent runs compare the same deterministic outcomes.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,stat,subprocess,sys,tempfile
HERE=Path(__file__).resolve().parents[2];PROJECT=HERE.parents[3]
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def observe(root):
 out={}
 for p in [root,*root.rglob('*')]:
  s=p.lstat();d={'mode':stat.S_IMODE(s.st_mode),'nlink':s.st_nlink,'kind':stat.S_IFMT(s.st_mode)}
  if stat.S_ISLNK(s.st_mode):d['target']=os.readlink(p)
  elif stat.S_ISREG(s.st_mode):d.update(size=s.st_size,sha256=h(p))
  out[str(p.relative_to(root))]=d
 return out

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--record',action='store_true');a=ap.parse_args()
 manifest=json.loads((HERE/'packet/MANIFEST.json').read_text());entries=manifest['entries']
 anchors={x:h(HERE/x) for x in ['FINAL.json','packet/MANIFEST.json','REPORT.md']}
 cases=['baseline','wrong-final-anchor','wrong-manifest-anchor','wrong-report-anchor','missing-anchor','flip-final','flip-manifest','flip-report','flip-review','flip-limits','flip-private-source','flip-private-primary','missing-review','extra-public','extra-empty-dir','symlink','hardlink','mode','fifo']
 results=[]
 with tempfile.TemporaryDirectory(prefix='.controls-',dir=HERE/'work') as temp:
  for case in cases:
   root=Path(temp)/case;root.mkdir()
   for rel,d in sorted(entries.items(),key=lambda x:(x[0].count('/'),x[0])):
    if rel=='.':continue
    p=root/rel
    if d['type']=='directory':p.mkdir(exist_ok=True);p.chmod(d['mode'])
    else:p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(HERE/rel,p);p.chmod(d['mode'])
   for rel in anchors:shutil.copyfile(HERE/rel,root/rel);(root/rel).chmod(0o644)
   root.chmod(entries['.']['mode'])
   mutate={'flip-final':'FINAL.json','flip-manifest':'packet/MANIFEST.json','flip-report':'REPORT.md','flip-review':'packet/public/review.md','flip-limits':'packet/public/reading-limits.md','flip-private-source':next(x for x in entries if x.startswith('packet/private/source/') and x.endswith('.tex')),'flip-private-primary':next(x for x in entries if x.startswith('packet/private/primary/') and x.endswith('.pdf'))}
   if case in mutate:
    p=root/mutate[case];p.write_bytes(p.read_bytes()+b'\ncontrol mutation\n')
   if case=='missing-review':(root/'packet/public/review.md').unlink()
   if case=='extra-public':(root/'packet/public/extra.txt').write_text('extra')
   if case=='extra-empty-dir':(root/'packet/public/extra-empty').mkdir()
   if case=='symlink':(root/'packet/public/extra-link').symlink_to('review.md')
   if case=='hardlink':os.link(root/'packet/public/review.md',root/'packet/public/extra-hardlink')
   if case=='mode':(root/'packet/public/review.md').chmod(0o600)
   if case=='fifo':os.mkfifo(root/'packet/public/extra-fifo')
   supplied=dict(anchors)
   for suffix,rel in [('final','FINAL.json'),('manifest','packet/MANIFEST.json'),('report','REPORT.md')]:
    if case=='wrong-'+suffix+'-anchor':supplied[rel]='0'*64
   cmd=[sys.executable,'-B',str(HERE/'packet/public/verify.py'),'--root',str(root),'--project',str(PROJECT),'--manifesthash',supplied['packet/MANIFEST.json'],'--reporthash',supplied['REPORT.md']]
   if case!='missing-anchor':cmd+=['--finalhash',supplied['FINAL.json']]
   before=observe(root);p=subprocess.run(cmd,capture_output=True,text=True,timeout=60);unchanged=before==observe(root)
   accepted=p.returncode==0;expected=accepted==(case=='baseline')
   results.append({'case':case,'accepted':accepted,'as_expected':expected,'copied_tree_unchanged':unchanged,'exit':p.returncode})
   assert expected and unchanged,(case,p.stdout,p.stderr)
   shutil.rmtree(root)
 out={'kind':'COPIED_REVIEW_SEAL_CONTROLS_NOT_MATHEMATICAL_GATE','cases':results,'all_expected':True,'read_only_observed':True,'coverage':'exact full persistent root, all three detached anchors, public/private payload, missing/extra entries, empty directory, symlink, hardlink, mode, FIFO; copies only; verifier output observed not syscall-denied','anchor_epoch':'same verifier and full payload design; suite rerun and compared after final seal; receipt omits variable hash values to avoid circular sealing'}
 target=HERE/'packet/public/control-results.json'
 if a.record:target.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
 else:assert json.loads(target.read_text())==out
 print(json.dumps({'cases':len(results),'all_expected':True,'receipt_matches':not a.record},sort_keys=True))
if __name__=='__main__':main()
