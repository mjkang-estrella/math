from pathlib import Path
import json,hashlib,shutil,zipfile,stat
L=Path(__file__).resolve().parents[1]; P=L.parent
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
roots=['expanded-corpus-r198','submodsep-review-r1','submodsep-retention-r1']
files=[]
for root in roots:
 files.extend(p for p in (P/root).rglob('*') if p.is_file() and not p.is_symlink())
files.extend(P/f'submodsep-root-ruling-r{i}.json' for i in (1,2))
for n in ['replay-result.json','registry-refresh.json']:
 p=P/'submodsep-parent-final-r1'/n
 if p.exists():files.append(p)
manifest={str(p.relative_to(P)):h(p) for p in sorted(files)}
(L/'receipts/inputs-before.json').write_text(json.dumps(manifest,indent=2)+'\n')
# Preserve the complete frozen lanes as evidence; no other target lanes are copied.
for root in roots:shutil.copytree(P/root,L/'evidence'/root,dirs_exist_ok=True)
for i in (1,2):shutil.copy2(P/f'submodsep-root-ruling-r{i}.json',L/'evidence')
p=L/'evidence/expanded-corpus-r198/lean-packet.zip'
assert h(p)=='441cb79ec825366931cdee6221b99e4b3235dd2145f343565e8df2fb2bd13db8'
shutil.copy2(p,L/'lean-packet.zip')
seen=set(); total=0
with zipfile.ZipFile(p) as z:
 for info in z.infolist():
  q=Path(info.filename)
  assert not q.is_absolute() and '..' not in q.parts and '\\' not in info.filename
  assert info.filename not in seen;seen.add(info.filename)
  assert not stat.S_ISLNK(info.external_attr>>16)
  total+=info.file_size;assert total<256*1024**2
  dest=L/'packet-safe'/q;assert dest.resolve().is_relative_to((L/'packet-safe').resolve())
  if info.is_dir():dest.mkdir(parents=True,exist_ok=True)
  else:
   dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(z.read(info))
(L/'receipts/safe-extraction.json').write_text(json.dumps({'pass':True,'packet_sha256':h(p),'entries':len(seen),'uncompressed_bytes':total,'lean_executed':False,'extracted_files':{str(x.relative_to(L/'packet-safe')):h(x) for x in (L/'packet-safe').rglob('*') if x.is_file()}},indent=2)+'\n')
print('Frozen',len(files),'files; safe packet extraction PASS')
