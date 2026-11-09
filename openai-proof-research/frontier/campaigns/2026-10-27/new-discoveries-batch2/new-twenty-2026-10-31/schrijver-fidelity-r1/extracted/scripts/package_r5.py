from pathlib import Path
import json,hashlib,re,zipfile,shutil
r=Path(__file__).resolve().parent.parent
before=json.loads((r/'frozen-before.json').read_text())
after={m:hashlib.sha256((r/'src'/m).read_bytes()).hexdigest() for m in before}
assert before==after
with zipfile.ZipFile(r/'../schrijver-formal-r4/schrijver-partial-source.zip') as z:
 for m,h in after.items():assert hashlib.sha256(z.read('src/'+m)).hexdigest()==h
(r/'frozen-after.json').write_text(json.dumps(after,indent=2))
sources={p.stem:p for p in (r/'src').glob('*.lean')};order=[];seen=set()
def visit(m):
 if m in seen:return
 seen.add(m)
 for i in re.findall(r'^import (\w+)',sources[m].read_text(),re.M):
  if i in sources:visit(i)
 order.append(m)
for m in sorted(sources):visit(m)
(r/'outputs/modules.json').write_text(json.dumps(order,indent=2))
files=[]
for directory in ['src','scripts','negative','inputs','outputs']:
 files.extend(p for p in (r/directory).rglob('*') if p.is_file())
files.extend(r/n for n in ['PROOF.md','STATEMENT-CORRESPONDENCE.md','REPRODUCE.md','SUMMARY.md','TASK.txt','frozen-before.json','frozen-after.json'])
manifest={str(p.relative_to(r)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)}
(r/'SOURCE-MANIFEST.json').write_text(json.dumps(manifest,indent=2))
zpath=r/'schrijver-source-r5.zip'
with zipfile.ZipFile(zpath,'w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted(files)+[r/'SOURCE-MANIFEST.json']:z.write(p,p.relative_to(r))
(r/'source-archive.sha256').write_text(hashlib.sha256(zpath.read_bytes()).hexdigest()+'  '+zpath.name+'\n')
fresh=r/'fresh-extraction-r5';assert not fresh.exists();fresh.mkdir()
with zipfile.ZipFile(zpath) as z:
 for n in z.namelist():assert not Path(n).is_absolute() and '..' not in Path(n).parts
 z.extractall(fresh)
print('PACKAGED',len(order),'modules; frozen',len(after))
