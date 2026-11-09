from pathlib import Path
import hashlib,json,stat,zipfile
D=Path(__file__).resolve().parents[1]
p=D/'338258-infinite-family-source.zip'
assert hashlib.sha256(p.read_bytes()).hexdigest()=='27175a85484d563031a12665736dbd4277de327cb726e1b6791d07a348c2c063'
out=D/'proof-packet-safe';out.mkdir(exist_ok=True);rows=[]
with zipfile.ZipFile(p) as z:
 assert len(z.namelist())==len(set(z.namelist()))==22
 for i in z.infolist():
  n=Path(i.filename)
  assert not n.is_absolute() and '..' not in n.parts and '\\' not in i.filename
  assert n.suffix=='.lean' and not stat.S_ISLNK(i.external_attr>>16) and i.file_size<2000000
  q=out/n;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(z.read(i))
  rows.append({'name':i.filename,'sha256':hashlib.sha256(q.read_bytes()).hexdigest()})
(D/'safe-extraction.json').write_text(json.dumps({'safe':True,'source_only':True,'modules':22,'Lean_executed':False,'members':rows},indent=2)+'\n')
print('Safe source-only extraction; no prover executed.')
