from pathlib import Path
import zipfile,hashlib
root=Path(__file__).resolve().parent.parent
paths=list(root.glob('StackSortSeeds2*.lean'))+list((root/'frozen').glob('*.lean'))+list((root/'scripts').glob('*.sh'))+list((root/'scripts').glob('*.py'))
paths += [root/x for x in ['TASK.txt','SUMMARY.md','PROOF.md','REPRODUCE.md','STATEMENT-CORRESPONDENCE.md','results.json','numeric.json','audit-summary.json','hashes/frozen-before.sha256','hashes/frozen-after.sha256','hashes/packet.sha256'] if (root/x).exists()]
archive=root/'stacksort-seeds2-source.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted(set(paths)):
  name=str(p.relative_to(root));assert not name.startswith('/') and '..' not in Path(name).parts
  z.write(p,name)
(root/'stacksort-seeds2-source.zip.sha256').write_text(hashlib.sha256(archive.read_bytes()).hexdigest()+'  stacksort-seeds2-source.zip\n')
print('Source-only archive:',len(paths),'safe files')
