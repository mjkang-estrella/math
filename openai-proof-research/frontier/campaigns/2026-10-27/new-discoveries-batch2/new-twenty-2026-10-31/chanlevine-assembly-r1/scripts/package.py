import pathlib,json,hashlib,zipfile
lane=pathlib.Path(__file__).resolve().parent.parent
result=json.loads((lane/'logs/build-result.json').read_text())
assert result['status']=='PASS' and len(result['sources'])==74
assert not (lane/'formal/ChanLevineFinal.lean').exists()
(lane/'formal/ChanLevineFinal.lean').write_bytes((lane/'scripts/final-template.lean.txt').read_bytes())
manifest={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((lane/'formal').glob('*.lean'))}
assert len(manifest)==75
(lane/'formal-manifest.json').write_text(json.dumps(manifest,indent=2))
frozen=json.loads((lane/'merge-manifest.json').read_text())['modules']
assert all(manifest[n]==r['sha256'] for n,r in frozen.items())
with zipfile.ZipFile(lane/'chanlevine-assembly-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted((lane/'formal').glob('*.lean')):z.write(p,p.relative_to(lane))
 for p in sorted((lane/'scripts').glob('*')):
  if p.is_file():z.write(p,p.relative_to(lane))
 for n in ['REPRODUCE.md','STATEMENT-CORRESPONDENCE.md','merge-manifest.json','formal-manifest.json','source-evidence.json','prior-handbacks-read.json']:
  z.write(lane/n,n)
print('Packaged 75 sources with frozen identity verified')
