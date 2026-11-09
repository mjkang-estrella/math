from pathlib import Path,PurePosixPath
import hashlib,json,zipfile,stat,shutil
w=Path(__file__).resolve().parent
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
zp=w/'frozen/330264-replay-fit-r2-source.zip'
assert h(zp)=='00c3713935d6a13f701cd3a26f9c7f1a86633e0eb60ff00a7ed0d100ea3d2fb5'
d=w/'proof';assert not d.exists();d.mkdir()
rows={}
with zipfile.ZipFile(zp) as z:
 assert len(z.infolist())==64 and len(set(z.namelist()))==64
 for i in z.infolist():
  p=PurePosixPath(i.filename)
  assert not p.is_absolute() and len(p.parts)==1 and p.suffix=='.lean' and '..' not in p.parts
  assert stat.S_IFMT(i.external_attr>>16) in [0,stat.S_IFREG]
  assert i.file_size<10000000
  data=z.read(i);f=d/p.name;f.write_bytes(data);assert f.read_bytes()==data
  rows[p.name]=h(f)
assert not list(d.glob('*.olean'))
import zipfile
with zipfile.ZipFile(w/'frozen/330264-r3-FULL-LEAN.zip') as old:
 for n in ['Endpoint.lean','GroupSemantics.lean']: assert (d/n).read_bytes()==old.read(n)
closure=json.loads((w/'reviews/replay-fit-r2/statement-closure.json').read_text())
assert len(closure['closure'])==10 and all(x['identical'] for x in closure['closure'])
(w/'packet-manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
(w/'safe-extraction-receipt.json').write_text(json.dumps({'packet_sha256':h(zp),'modules':64,'safe_paths':True,'regular_files_only':True,'no_objects':True,'each_extracted_byte_verified':True,'Endpoint_and_GroupSemantics_byte_identical_to_historical_archive':True,'Lean_run':False},indent=2)+'\n')
raw=w/'sources/330264.raw.jsonl';bindings=json.loads((w/'reviews/held-reopen-r1/literal-bindings.json').read_text());bind=next(x for x in bindings if x['id']=='330264')
# independently bind corpus bytes without modifying the corpus.
corpus=Path(bind['path']);ch=h(corpus);line=corpus.read_bytes().splitlines(keepends=True)[4739]
assert ch==bind['chunk_sha256'] and line==raw.read_bytes() and h(raw)==bind['line_sha256']
(w/'literal-binding.json').write_text(json.dumps(bind,indent=2)+'\n')
(w/'corpus-integrity-before.json').write_text(json.dumps({'path':str(corpus),'sha256':ch,'line':4740,'line_sha256':h(raw)},indent=2)+'\n')
# Adapt arithmetic checker to split data modules, leaving checks unchanged.
s=(w.parent/'coxeter-manuscript-r1/independent-corroboration.py').read_text()
s=s.replace("sw=(f/'SpectralWitness.lean').read_text()", "sw='\\n'.join((f/('Spectral'+tag+'Data.lean')).read_text() for tag in ['A','C','L'])")
(w/'independent-corroboration.py').write_text(s)
print('PASS safe extraction: 64 modules; historical endpoint bytes; raw corpus chunk and line')
