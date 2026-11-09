import pathlib,json,hashlib,zipfile
D=pathlib.Path(__file__).resolve().parents[1];mods=['Core']+[f'Row{i}' for i in range(15)]+['Table','Endpoint','Audit'];data={m+'.lean':(D/f'formal/{m}.lean').read_bytes() for m in mods};data['README.md']=b'Candidate refutation of MathDB 338258, not accepted. Endpoint: Riordan.source_conjecture_false. Compile Core, Row0..Row14, Table, Endpoint, Audit with pinned Lean 4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. See lane scripts/replay.py and RIORDAN-PROOF.md. Cached upstream oleans are trusted, not rebuilt.\n';data['MANIFEST.json']=(json.dumps({n:hashlib.sha256(b).hexdigest() for n,b in data.items()},indent=2)+'\n').encode()
with zipfile.ZipFile(D/'338258-proof-source.zip','w',compression=zipfile.ZIP_DEFLATED) as z:
 for n,b in sorted(data.items()):
  i=zipfile.ZipInfo(n,(1980,1,1,0,0,0));i.external_attr=0o100644<<16;z.writestr(i,b)
print(hashlib.sha256((D/'338258-proof-source.zip').read_bytes()).hexdigest())
