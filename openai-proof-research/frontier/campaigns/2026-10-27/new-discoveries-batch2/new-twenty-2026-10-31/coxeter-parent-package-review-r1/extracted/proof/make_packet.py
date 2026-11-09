from pathlib import Path
import hashlib,json,zipfile,datetime
w=Path(__file__).resolve().parent
files=[p for p in w.iterdir() if p.is_file() and (p.suffix in ['.lean','.py','.md'] or p.name in ['README-replay.txt','input-bindings.json','provenance.json','330264.literal.json','dependency-hashes.json','input-verification-before.json','input-verification-after.json','results.json','replay-receipt.json','new-counts.json'])]
files += list((w/'sources').glob('*'))
manifest={'scope':'FULL_LEAN_ENDPOINT; novelty and acceptance independent','mathlib_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612','lean':'4.34.1','files':{str(p.relative_to(w)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)}}
(w/'packet-manifest.json').write_text(json.dumps(manifest,indent=2))
with zipfile.ZipFile(w/'330264-r3-FULL-LEAN.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in files+[w/'packet-manifest.json']:z.write(p,p.relative_to(w))
print('Packet:',len(files),'files')
