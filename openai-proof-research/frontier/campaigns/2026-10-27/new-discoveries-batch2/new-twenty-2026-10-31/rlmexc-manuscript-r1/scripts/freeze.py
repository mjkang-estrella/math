from pathlib import Path
import hashlib,json,shutil,sys
r=Path.cwd(); p=r.parent
paths=[p/'rlmexc-root-ruling-r1.json',p/'expanded-corpus-r204/CANDIDATE-350721.md',p/'expanded-corpus-r204/SUMMARY.md',p/'expanded-corpus-r204/results.json',p/'expanded-corpus-r204/raw/350721.jsonl']
for lane in ['rlmexc-review-r1','rlmexc-formal-r1','rlmexc-root-check-r1']:
 paths += [f for f in (p/lane).rglob('*') if f.is_file() and not f.is_symlink()]
for sub in ['sources/ajc','sources/tex/2105.08455','sources/tex/2206.11236','outputs','scripts']:
 paths += [f for f in (p/'expanded-corpus-r204'/sub).rglob('*') if f.is_file()]
paths += [p/'rlmexc-parent-final-r1'/s for s in ['replay-result.json','registry-refresh.json']]
paths += [p/'AGENTS.md',p.parent/'AGENTS.md',Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/AGENTS.md'),r/'TASK.txt']
h={str(f):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(set(paths))}
if sys.argv[1]=='before':
 (r/'receipts/input-hashes-before.json').write_text(json.dumps(h,indent=2)+'\n')
 for f in sorted(set(paths)):
  if '/replay/' in str(f) or f.suffix in ['.olean','.ilean']: continue
  dest=r/'inputs'/f.relative_to(p) if f.is_relative_to(p) else r/'inputs/rules'/f.name
  dest.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(f,dest)
 shutil.copyfile(p/'rlmexc-formal-r1/source.zip',r/'lean-source.zip')
else:
 (r/'receipts/input-hashes-after.json').write_text(json.dumps(h,indent=2)+'\n')
 assert h==json.loads((r/'receipts/input-hashes-before.json').read_text())
print('frozen inputs',len(h),sys.argv[1])
