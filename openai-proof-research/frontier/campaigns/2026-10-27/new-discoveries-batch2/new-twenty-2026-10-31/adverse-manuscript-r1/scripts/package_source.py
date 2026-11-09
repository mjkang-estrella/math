from pathlib import Path
import zipfile,hashlib,json,stat
R=Path(__file__).resolve().parents[1]
files=[R/'replay.py',R/'MODULE-HASHES.json',R/'REPRODUCE.md',R/'PROOF.md',R/'STATEMENT-CORRESPONDENCE.md']+list((R/'formal').glob('*.lean'))+[R/'scripts'/s for s in ['bounded.py','lean.sh','checker.sh']]
files += [R/'paper/manuscript.py']
files += [R/'inputs/outputs/latin36-certificate.json',R/'inputs/raw/381433.jsonl']
manifest={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
(R/'SOURCE-MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n');files +=[R/'SOURCE-MANIFEST.json']
z=R/'adverse-381433-manuscript-source.zip'
with zipfile.ZipFile(z,'w',zipfile.ZIP_DEFLATED) as f:
 for p in sorted(files):f.write(p,p.relative_to(R))
D=R/'fresh-replay';D.mkdir()
with zipfile.ZipFile(z) as f:
 for i in f.infolist():
  p=Path(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and not stat.S_ISLNK(i.external_attr>>16)
  assert not any(q in i.filename for q in ['.olean','.ilean'])
 f.extractall(D)
assert all(hashlib.sha256((D/p).read_bytes()).hexdigest()==h for p,h in manifest.items())
(R/'receipts/source-extraction.json').write_text(json.dumps({'safe_extraction':'PASS','zip_sha256':hashlib.sha256(z.read_bytes()).hexdigest(),'manifest_verified':True,'files':len(files)},indent=2)+'\n')
