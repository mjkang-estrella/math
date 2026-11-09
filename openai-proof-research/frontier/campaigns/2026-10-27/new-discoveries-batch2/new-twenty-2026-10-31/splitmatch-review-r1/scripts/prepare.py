from pathlib import Path
import zipfile,hashlib,json
L=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/splitmatch-review-r1')
D=L.parent/'expanded-corpus-r168'
p=D/'Lean-packet.zip'
assert hashlib.sha256(p.read_bytes()).hexdigest()=='26696a02df86785f733fc4242447abdd1b2206aeff0f8300183c14d84d132ca5'
out=L/'extracted';out.mkdir()
with zipfile.ZipFile(p) as z:
 for f in z.infolist():
  dest=out/f.filename
  assert dest.resolve().is_relative_to(out.resolve()) and not (f.external_attr>>16 & 0o170000)==0o120000
  assert f.file_size<20000000
  if f.is_dir():dest.mkdir(parents=True,exist_ok=True)
  else:dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(z.read(f))
for name in ['SplitMatching.lean','Audit.lean']:
 (L/'build'/name).write_bytes((out/'lean'/name).read_bytes())
r=json.loads((D/'results.json').read_text())['381751']
(L/'mathdb-entry.json').write_text(json.dumps(r,indent=2))
print(json.dumps(r,indent=2))
