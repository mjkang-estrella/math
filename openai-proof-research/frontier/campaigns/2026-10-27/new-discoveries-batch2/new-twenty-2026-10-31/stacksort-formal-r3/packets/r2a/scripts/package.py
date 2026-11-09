import pathlib,zipfile
lane=pathlib.Path(__file__).resolve().parent.parent
files=sorted(lane.glob('*.lean'))+sorted((lane/'scripts').glob('*'))
files += [lane/x for x in ['SUMMARY.md','PROOF.md','STATEMENT-CORRESPONDENCE.md','REPRODUCE.md','lower-table.json']]
with zipfile.ZipFile(lane/'stacksort-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in files:
  if p.is_file():z.write(p,p.relative_to(lane).as_posix())
dest=lane/'fresh-extraction'
dest.mkdir()
assert not list(dest.iterdir())
with zipfile.ZipFile(lane/'stacksort-source.zip') as z:
 for name in z.namelist():
  p=pathlib.PurePosixPath(name)
  assert not p.is_absolute() and '..' not in p.parts
 z.extractall(dest)
for p in (dest/'scripts').glob('*.sh'):p.chmod(0o755)
print('safe source-only archive; fresh empty extraction')
