from pathlib import Path,PurePosixPath
import sys,json,hashlib,zipfile,stat,shutil
D=Path(sys.argv[1]).resolve();r=json.loads((D/'packet-reuse-receipt.json').read_text());packet=Path(sys.argv[2]) if len(sys.argv)>2 else Path(r['path'])
def sha(f):
 h=hashlib.sha256()
 with f.open('rb') as a:
  for b in iter(lambda:a.read(1048576),b''):h.update(b)
 return h.hexdigest()
assert sha(packet)==r['sha256'];root=D/'tmp/packet-test';assert not root.exists();root.mkdir(parents=True)
try:
 with zipfile.ZipFile(packet) as z:
  infos=z.infolist();assert len({i.filename for i in infos})==len(infos)
  assert sum(i.file_size for i in infos)==r['uncompressed_bytes']
  for i in infos:
   p=PurePosixPath(i.filename);assert not p.is_absolute() and '..' not in p.parts and '\\' not in i.filename and not stat.S_ISLNK(i.external_attr>>16) and i.file_size<150000000
   f=root.joinpath(*p.parts);f.parent.mkdir(parents=True,exist_ok=True)
   if not i.is_dir():
    with z.open(i) as a,f.open('wb') as b:shutil.copyfileobj(a,b,1048576)
  count=0
  for line in (root/'source-manifest.sha256').read_text().splitlines():
   expected,name=line.split(maxsplit=1);assert sha(root/name.lstrip('*'))==expected;count+=1
  assert len((root/'module-order.txt').read_text().splitlines())==830
 result=dict(status='PASS',archive_sha256=sha(packet),manifest_entries=count,modules=830,no_lean_run=True,no_archive_copy=True)
finally:shutil.rmtree(root)
(D/'packet-safety-repeat.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
