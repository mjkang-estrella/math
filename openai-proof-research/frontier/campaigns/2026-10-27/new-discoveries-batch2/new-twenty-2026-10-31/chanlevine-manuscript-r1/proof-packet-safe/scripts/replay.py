import pathlib,zipfile,time,json,hashlib,subprocess,sys
lane=pathlib.Path(__file__).resolve().parent.parent
archive=lane/'chanlevine-assembly-source.zip'
dest=lane/f'replay-{time.time_ns()}'
dest.mkdir()
with zipfile.ZipFile(archive) as z:
 for n in z.namelist():
  p=pathlib.PurePosixPath(n)
  assert not p.is_absolute() and '..' not in p.parts and '\\' not in n
 z.extractall(dest)
manifest=json.loads((dest/'formal-manifest.json').read_text())
assert {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (dest/'formal').glob('*.lean')}==manifest
assert len(manifest)==75
frozen=json.loads((dest/'merge-manifest.json').read_text())['modules']
assert all(manifest[n]==v['sha256'] for n,v in frozen.items())
log=lane/'logs'/f'fresh-replay-driver-{time.time_ns()}.log'
with log.open('w') as f:
 p=subprocess.run([sys.executable,'-I',str(dest/'scripts/validate.py'),str(dest)],stdout=f,stderr=subprocess.STDOUT)
receipt={'directory':str(dest),'archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'driver_log':str(log),'returncode':p.returncode,'safe_paths':True,'fresh_sources_match':True}
(lane/'logs/latest-replay.json').write_text(json.dumps(receipt,indent=2))
print(json.dumps(receipt,indent=2));sys.exit(p.returncode)
