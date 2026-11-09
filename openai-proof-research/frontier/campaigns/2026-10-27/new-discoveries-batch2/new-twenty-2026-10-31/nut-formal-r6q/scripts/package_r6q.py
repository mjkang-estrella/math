from pathlib import Path
import json,hashlib,zipfile
r=Path(__file__).resolve().parents[1]
files=list((r/'formal').glob('*.lean'))+list((r/'scripts').glob('*.py'))
files += [p for p in r.iterdir() if p.is_file() and p.suffix in ['.md','.json','.py'] and p.name not in ['packet-manifest.json','launch.json','development-build.json']]
files += [p for p in (r/'inputs').rglob('*') if p.is_file()]
files=sorted(set(files));assert not any(p.suffix in ['.olean','.ilean','.pyc'] for p in files)
manifest={str(p.relative_to(r)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
(r/'packet-manifest.json').write_text(json.dumps({'source_only':True,'files':manifest},indent=2)+'\n');files.append(r/'packet-manifest.json')
with zipfile.ZipFile(r/'nut-r6q-source.zip','w',compression=zipfile.ZIP_DEFLATED) as z:
 for p in files:z.write(p,p.relative_to(r))
h=hashlib.sha256((r/'nut-r6q-source.zip').read_bytes()).hexdigest();(r/'nut-r6q-source.zip.sha256').write_text(h+'  nut-r6q-source.zip\n');print('Packet',h,len(files),'files')
