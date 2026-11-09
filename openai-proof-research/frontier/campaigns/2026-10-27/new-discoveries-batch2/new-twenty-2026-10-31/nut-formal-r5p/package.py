from pathlib import Path
import zipfile,hashlib,json
r=Path(__file__).resolve().parent
files=list((r/'formal').glob('*.lean'))+[r/'replay.py',r/'modules.json',r/'inputs-before.json',r/'r4a-compatibility.json',r/'REPRODUCE.md',r/'GAPS.md',r/'SUMMARY.md',r/'statement-correspondence.md']+list((r/'scripts').glob('*.py'))
files += [r/'inputs/nut-formal-r2/all-normalized-certificates.json',r/'inputs/nut-formal-r4b/graph-extensions.json',r/'inputs/nut-formal-r4b/root-integration.json']
with zipfile.ZipFile(r/'nut-r5p-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in files:
  if p.exists():z.write(p,p.relative_to(r))
p=r/'nut-r5p-source.zip';(r/'nut-r5p-source.zip.sha256').write_text(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.name+'\n')
