from pathlib import Path
import hashlib,json,zipfile,stat,sys
R=Path(sys.argv[1]); D=R.parent/'expanded-corpus-r178'
files=[D/'CANDIDATE.md',D/'SUMMARY.md',D/'Lean-packet.zip',D/'results.json',D/'raw/360905.jsonl']+list((D/'sources').rglob('*'))+list((D/'lean').glob('*'))
hashes={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in files if p.is_file()}
(R/'inputs-before.json').write_text(json.dumps(hashes,indent=2))
with zipfile.ZipFile(D/'Lean-packet.zip') as z:
 for i in z.infolist():
  p=Path(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and not stat.S_ISLNK(i.external_attr>>16)
  assert i.file_size<20_000_000
  print(i.filename,i.file_size)
  if not i.is_dir():
   t=R/'replay'/p;t.parent.mkdir(parents=True,exist_ok=True);t.write_bytes(z.read(i))
print(json.dumps(json.loads((D/'results.json').read_text())['360905'],indent=2))
