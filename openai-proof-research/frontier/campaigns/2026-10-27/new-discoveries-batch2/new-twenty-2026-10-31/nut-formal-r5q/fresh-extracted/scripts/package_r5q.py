from pathlib import Path
import zipfile,hashlib,json
r=Path(__file__).resolve().parents[1]
files=list((r/'formal').glob('*.lean'))+list((r/'scripts').glob('*.py'))
files += [r/n for n in ['SUMMARY.md','GAPS.md','REPRODUCE.md','statement-correspondence.md','replay.py','modules.json','tree-modules.json','reconciliation.json','support-transport.json','inputs-before.json']]
if (r/'results.json').exists():files.append(r/'results.json')
if (r/'inputs-after.json').exists():files.append(r/'inputs-after.json')
# The assigned copies are evidence; no compiled files or recursive histories.
files+= [p for p in (r/'inputs').rglob('*') if p.is_file()]
assert not any(p.suffix in ['.olean','.ilean','.pyc'] for p in files)
manifest={str(p.relative_to(r)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)}
(r/'packet-manifest.json').write_text(json.dumps({'source_only':True,'files':manifest},indent=2)+'\n')
files.append(r/'packet-manifest.json')
with zipfile.ZipFile(r/'nut-r5q-source.zip','w',compression=zipfile.ZIP_DEFLATED) as z:
 for p in sorted(files):z.write(p,p.relative_to(r))
h=hashlib.sha256((r/'nut-r5q-source.zip').read_bytes()).hexdigest()
(r/'nut-r5q-source.zip.sha256').write_text(h+'  nut-r5q-source.zip\n')
print(h,len(files))
