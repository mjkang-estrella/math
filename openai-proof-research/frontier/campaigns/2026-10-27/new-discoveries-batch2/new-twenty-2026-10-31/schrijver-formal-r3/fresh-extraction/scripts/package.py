from pathlib import Path,PurePosixPath
import json,hashlib,zipfile
root=Path(__file__).resolve().parent.parent
source=[p for d in ['src','scripts','negative'] for p in (root/d).glob('*') if p.is_file()]
source += [root/f for f in ['SUMMARY.md','STATEMENT-CORRESPONDENCE.md','PROOF.md','REPRODUCE.md','TASK.txt']]
manifest={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(source)}
(root/'SOURCE-MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
files=source+[root/'SOURCE-MANIFEST.json']
files += [p for p in (root/'outputs').glob('*.json')]
files += [p for p in (root/'inputs').rglob('*') if p.is_file() and p.suffix in ['.json','.md','.txt','.py','.sh']]
if (root/'results.json').exists():files.append(root/'results.json')
archive=root/'schrijver-partial-source.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted(set(files)):
  rel=p.relative_to(root).as_posix();assert not PurePosixPath(rel).is_absolute() and '..' not in PurePosixPath(rel).parts
  assert not p.is_symlink()
  z.write(p,rel)
print(json.dumps(dict(archive=str(archive),files=len(set(files)),sha256=hashlib.sha256(archive.read_bytes()).hexdigest())))
