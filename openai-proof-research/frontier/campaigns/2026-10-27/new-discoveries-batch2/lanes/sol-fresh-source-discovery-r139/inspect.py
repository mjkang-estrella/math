from pathlib import Path
import tarfile,json,hashlib,datetime
L=Path(__file__).resolve().parent
with tarfile.open(L/'sources/achour-source.tar.gz') as t:
 for m in t.getmembers():
  if m.isfile():
   assert m.size<1000000
   b=t.extractfile(m).read()
   print(m.name,len(b))
   if m.name.endswith('.tex'):(L/'sources'/Path(m.name).name).write_bytes(b)
for n in ['omega-head.json','openai-head.json']:
 j=json.loads((L/'sources'/n).read_bytes());print(n,j['sha'],j['commit']['committer']['date'])
j=json.loads((L/'sources/omega-delta.json').read_bytes())
print({k:j[k] for k in ['status','total_commits','ahead_by','behind_by']})
print('delta paths',[f['filename'] for f in j['files']])
