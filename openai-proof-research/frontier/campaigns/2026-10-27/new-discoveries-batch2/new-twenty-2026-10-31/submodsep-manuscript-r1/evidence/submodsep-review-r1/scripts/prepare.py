from pathlib import Path
import zipfile,hashlib,json
L=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/submodsep-review-r1');D=L.parent/'expanded-corpus-r198'
out=L/'build'/'fresh';out.mkdir()
with zipfile.ZipFile(D/'lean-packet.zip') as z:
 for i in z.infolist():
  p=Path(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and i.file_size<1000000 and (i.external_attr>>16)&0o170000!=0o120000
  t=out/p;t.parent.mkdir(parents=True,exist_ok=True);t.write_bytes(z.read(i))
inputs=[p for p in D.rglob('*') if p.is_file() and (p.suffix in ['.lean'] or '341850' in str(p) or 'csp-' in str(p) or p.name in ['extracted.json','source-versions.json','registry-screen.json'])]
(L/'extra-before.json').write_text(json.dumps({str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs},indent=2))
print('Safe extraction complete',len(inputs),'extra inputs hash-bound')
print(json.dumps(json.loads((D/'outputs/source-versions.json').read_text())['341850'],indent=2))
print(json.dumps(json.loads((D/'results.json').read_text()),indent=2)[:1000])
